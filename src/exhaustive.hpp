#include "internal.hpp"
#include <type_traits>
#include <deque>
#include <vector>
#include <functional>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <cassert>
#include <unordered_set>

// wyhash helpers (fast, inline, no external dependencies)
static inline void _es_wymix(uint64_t &A, uint64_t &B) {
    __uint128_t r = (__uint128_t)A * B;
    A = (uint64_t)r;
    B = (uint64_t)(r >> 64);
}
static inline uint64_t es_wyhash(const void* key, size_t len, uint64_t seed) {
    const uint8_t* p = (const uint8_t*)key;
    seed ^= 0x9e3779b97f4a7c15ULL;
    uint64_t a = 0, b = 0;
    if (len <= 16) {
        if (len >= 4) {
            uint32_t lo, hi, ml, mr;
            memcpy(&lo, p,           4);
            memcpy(&hi, p + len - 4, 4);
            memcpy(&ml, p + (len >> 1) - 2, 4);
            memcpy(&mr, p + len - (len >> 1) + 2 - 4, 4);
            a = (uint64_t)lo | ((uint64_t)hi << 32);
            b = (uint64_t)ml | ((uint64_t)mr << 32);
        } else if (len > 0) {
            a = p[0] | ((uint64_t)p[len >> 1] << 8) | ((uint64_t)p[len - 1] << 16);
        }
    } else {
        size_t i = len;
        if (i > 48) {
            uint64_t see1 = seed, see2 = seed;
            do {
                uint64_t w0,w1,w2,w3,w4,w5;
                memcpy(&w0,p,8); memcpy(&w1,p+8,8); memcpy(&w2,p+16,8);
                memcpy(&w3,p+24,8); memcpy(&w4,p+32,8); memcpy(&w5,p+40,8);
                uint64_t t0=seed^w0, t1=see1^w1; _es_wymix(t0,t1); seed=t0; see1=t1;
                uint64_t t2=see2^w2, t3=seed^w3; _es_wymix(t2,t3); see2=t2; seed=t3;
                uint64_t t4=seed^w4, t5=see1^w5; _es_wymix(t4,t5); seed=t4; see1=t5;
                p += 48; i -= 48;
            } while (i > 48);
            seed ^= see1 ^ see2;
        }
        while (i > 16) {
            uint64_t w0, w1;
            memcpy(&w0, p, 8); memcpy(&w1, p+8, 8);
            uint64_t t0=seed^w0, t1=seed^w1; _es_wymix(t0,t1); seed=t0;
            p += 16; i -= 16;
        }
        memcpy(&a, p + i - 16, 8);
        memcpy(&b, p + i - 8,  8);
    }
    uint64_t t0 = a ^ 0xa0761d6478bd642fULL ^ seed;
    uint64_t t1 = b ^ 0xe7037ed1a0b428dbULL;
    _es_wymix(t0, t1);
    return t0 ^ t1;
}

struct ExhaustiveSearchOptions {
    std::vector<int> to_observe;

    bool only_neg = false;
    bool can_forget = false;
    bool track_solutions = false;
    bool output_solutions = false;

    FILE* solfile = nullptr;
    
    void (*solution_callback)(const std::vector<int>&) = nullptr;
}; 

struct GenericSolutionProcessor {
    void (*cb)(const std::vector<int>&) = nullptr;

    void operator()(const std::vector<int>& solution) const {
        if (cb) cb(solution);
    }

    explicit operator bool() const { return cb != nullptr; }
};

/**
 * @brief Exhaustive search over a subset of variables using CaDiCaL's external propagator.
 *
 * This class enumerates all partial assignments to a user-specified set of "observed" variables
 * that can be extended to a full satisfying assignment of the original formula.
 * It integrates with CaDiCaL as an ExternalPropagator, tracking assignments and adding
 * blocking clauses to prune the search space. Uses hashing to only record unique solutions.
 *
 * @warning Potential false positives: The current implementation may record a "solution"
 *          as soon as all observed variables have been assigned, before the solver has
 *          fully verified consistency of the remaining unobserved clauses. In particular,
 *          if the solver later discovers a conflict (e.g., a failed assumption or a falsified
 *          clause among unobserved variables), a false solution may already have been counted
 *          and an incorrect blocking clause added. This can lead to over‑counting of solutions
 *          and, in rare cases, missed genuine solutions.
 *
 * @note   When is this safe? If the unobserved part of the formula is known to be
 *         empty or trivially satisfiable for any assignment to the observed variables (e.g., 
 *         no clauses involve unobserved variables), so this early blocking is sound and offers
 *         the best performance. In all other cases, use with caution.
 *
 * @note   Performance: This early‑blocking strategy is typically the fastest method
 *         for exhaustive enumeration because it prunes the search tree as soon as the
 *         observed variables are fully assigned. Waiting for a full model (via
 *         cb_check_found_model) is sound but may explore many extensions before pruning,
 *         greatly slowing the solving.
 *
 * @see    CaDiCaL::ExternalPropagator
 */
template <typename SolutionProcessor = GenericSolutionProcessor>
class ExhaustiveSearch : CaDiCaL::ExternalPropagator {
    CaDiCaL::Solver* solver;

    size_t assigned_count = 0;
    std::vector<int> assignment;
    std::deque<std::vector<int>> assignments_by_level;
    std::vector<std::vector<int>> new_clauses;
    
    long sol_count = 0;
    std::vector<std::vector<int>> solutions;
    std::unordered_set<uint64_t> seen_hashes; // Deduplication: wyhash of the set of positive variables in the solution

	// options:
    FILE * solfile;
    std::vector<int> observed;
    bool only_neg = false;
    bool can_forget = false;
    bool track_solutions = false;
    bool output_solutions = false;
    
    SolutionProcessor processor_; // called whenever a new solution is found and passes it onto the callback function
    
public:
    ExhaustiveSearch(CaDiCaL::Solver * s, const ExhaustiveSearchOptions& opts, SolutionProcessor proc = SolutionProcessor{});
    ExhaustiveSearch(CaDiCaL::Solver * s);
    ~ExhaustiveSearch ();
    void notify_assignment(const std::vector<int>& lits);
    void notify_new_decision_level ();
    void notify_backtrack (size_t new_level);
    bool cb_check_found_model (const std::vector<int>& model) { (void)model; return false; };
    bool cb_has_external_clause (bool& is_forgettable);
    int cb_add_external_clause_lit ();
    int cb_decide () { return 0; };
    int cb_propagate () { return 0; };
    int cb_add_reason_clause_lit (int plit) { (void)plit; return 0; };
    long get_solution_count() const { return sol_count; }
    const std::vector<std::vector<int>>& get_solutions() const { return solutions; }
    void clear_solutions() { solutions.clear(); sol_count = 0; seen_hashes.clear(); }

private:
    void block_partial_solution();
};


template <typename SolutionProcessor>
ExhaustiveSearch<SolutionProcessor>::ExhaustiveSearch(CaDiCaL::Solver * s, const ExhaustiveSearchOptions& opts, SolutionProcessor proc) : solver(s), solfile(opts.solfile), only_neg(opts.only_neg), 
        can_forget(opts.can_forget), track_solutions(opts.track_solutions), output_solutions(opts.output_solutions), processor_(std::move(proc)) {
    if (opts.to_observe.empty()) { // No order provided; run exhaustive search on all variables
        observed.reserve(s->vars());
        for(int i=0; i < s->vars(); i++)
            observed.push_back(i+1);
    }
    else 
        observed = opts.to_observe;
    
    assignment.assign(s->vars(), 0);
    assignments_by_level.push_back({});
    
    solver->connect_external_propagator(this);
    
    //std::cout << "c Running exhaustive search on " << observed.size() << " variables" << std::endl;
    
    for (int var : observed)
        solver->add_observed_var(var);
        
    if constexpr (std::is_same_v<SolutionProcessor, GenericSolutionProcessor>)
        processor_.cb = opts.solution_callback; // take the pointer
    
}

template <typename SolutionProcessor>
ExhaustiveSearch<SolutionProcessor>::ExhaustiveSearch(CaDiCaL::Solver * s) : ExhaustiveSearch(s, {}, {}) { }

template <typename SolutionProcessor>
ExhaustiveSearch<SolutionProcessor>::~ExhaustiveSearch () {
    if (!observed.empty())
        solver->disconnect_external_propagator ();
        //std::cout << "c Number of solutions: " << sol_count << std::endl;
}

template <typename SolutionProcessor>
void ExhaustiveSearch<SolutionProcessor>::notify_assignment(const std::vector<int>& lits) {
    for (int lit : lits) { // Track assignments of observed variables
        int idx = abs(lit) - 1;
        if (assignment[idx] == 0) { // Variable not yet assigned
            assignment[idx] = lit; // Store the signed literal
            assigned_count++; // Increment total assigned variables
            assignments_by_level.back().push_back(lit); // Store when this literal was assigned
        }
    }    
}

template <typename SolutionProcessor>
void ExhaustiveSearch<SolutionProcessor>::notify_new_decision_level () {
    assignments_by_level.push_back({}); // Add new vector to track history
}

template <typename SolutionProcessor>
void ExhaustiveSearch<SolutionProcessor>::notify_backtrack (size_t new_level) {
    while (assignments_by_level.size() > new_level + 1) {
        std::vector<int>& lits_to_undo = assignments_by_level.back(); // History to wipe
        for (int lit : lits_to_undo) {
            int idx = abs(lit) - 1;
            assignment[idx] = 0; 
            assigned_count--;
        }
        assignments_by_level.pop_back(); // Remove history from list
    }
}

template <typename SolutionProcessor>
void ExhaustiveSearch<SolutionProcessor>::block_partial_solution() {
    std::vector<int> clause;
    std::vector<int> pos_vars; // Positive variable numbers of this solution
    clause.reserve(observed.size() + 1);
    pos_vars.reserve(observed.size());
    
    for (int var : observed) {
        int lit = assignment[var - 1];

        if (lit == 0)
            continue;

        if (lit > 0)
            pos_vars.push_back(var);
        if (lit > 0 || !only_neg)
            clause.push_back(-lit);
    }

    static constexpr uint64_t kHashSeed = 0x517cc1b727220a95ULL;
    uint64_t h = can_forget ? es_wyhash(pos_vars.data(), pos_vars.size() * sizeof(int), kHashSeed) : 0; // wyhash the raw bytes of the pos_vars vector (order is deterministic: observed order).

    bool is_new = !can_forget || seen_hashes.insert(h).second; // Duplication check

    if (is_new) { // Is unique solution so we record it
        sol_count++;
        solver->set_num_sol(sol_count);

        // Write to file (always a complete line) and/or console (if output_solutions)
        if (solfile) {
            for (int var : pos_vars)
                fprintf(solfile, "%d ", var);
            fputs("0\n", solfile);
        }
        if (output_solutions) {
            std::cout << "c New solution: ";
            for (int var : pos_vars)
                std::cout << var << " ";
            std::cout << "0\n";
        }

        if(processor_)
            processor_(pos_vars);

        if (track_solutions)
            solutions.push_back(std::move(pos_vars));
    }

    new_clauses.push_back(std::move(clause)); // Always add the blocking clause regardless of duplication, otherwise the solver would find the same assignment again
    solver->add_trusted_clause(new_clauses.back());
}

template <typename SolutionProcessor>
bool ExhaustiveSearch<SolutionProcessor>::cb_has_external_clause (bool& is_forgettable) {
    is_forgettable = can_forget;
    if (assigned_count == observed.size()) // Found all assignments and no solution found
        block_partial_solution();
    else
        return false;

    return true;
}

template <typename SolutionProcessor>
int ExhaustiveSearch<SolutionProcessor>::cb_add_external_clause_lit () {
    if (new_clauses.empty()) 
        return 0;
    else {
        size_t clause_idx = new_clauses.size() - 1;
        if (new_clauses[clause_idx].empty()) {
            new_clauses.pop_back();
            return 0;
        }

        int lit = new_clauses[clause_idx].back();
        new_clauses[clause_idx].pop_back();
        return lit;
    }
}