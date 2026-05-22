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

    // Call ExhaustiveSearch::set_assumptions() (and solver->assume() for each literal) before every new solve() call.
    std::vector<int> assumptions; // literals that must hold for the current solve call. 

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

    std::vector<int> pos_vars_buf_;
    std::vector<int> clause_buf_;
    size_t pending_pos_ = 0;
    
    long sol_count = 0;
    long global_sol_count = 0;
    std::vector<std::vector<int>> solutions;
    std::unordered_set<uint64_t> seen_hashes; // Deduplication: wyhash of the set of positive variables in the solution

    // options:
    FILE * solfile;
    std::vector<int> observed;
    std::vector<bool> is_observed_;
    bool only_neg = false;
    bool can_forget = false;
    bool track_solutions = false;
    bool output_solutions = false;
    
    std::vector<int> assumptions_; // to ensure backtracks do not falsify assumptions
    std::vector<int> assumption_lit_; // assumption_lit_[var-1] = required literal, or 0
    int violated_assumptions_ = 0;
    
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
    long get_global_solution_count() const { return global_sol_count; }
    const std::vector<std::vector<int>>& get_solutions() const { return solutions; }
    void clear_solutions() { solutions.clear(); sol_count = 0; seen_hashes.clear(); }
    void set_assumptions(const std::vector<int>& assumptions);
    void reset() {
        clear_solutions();
        pos_vars_buf_.clear();
        clause_buf_.clear();
        pending_pos_ = 0;

        assumptions_.clear();
        assumption_lit_.assign(is_observed_.size(), 0);
        violated_assumptions_ = 0;

        assigned_count = 0;
        std::fill(assignment.begin(), assignment.end(), 0);

        assignments_by_level.clear();
        assignments_by_level.push_back({});
    }

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
    
    assigned_count = 0;
    assignment.assign(s->vars(), 0);
    is_observed_.assign(s->vars(), false);
    assignments_by_level.push_back({});
    
    solver->connect_external_propagator(this);

    pos_vars_buf_.reserve(observed.size());
    clause_buf_.reserve(observed.size() + 1);
    
    //std::cout << "c Running exhaustive search on " << observed.size() << " variables" << std::endl;
    
    for (int var : observed) {
        solver->add_observed_var(var);
        is_observed_[var - 1] = true;
    }

    if(!opts.assumptions.empty())
        set_assumptions(opts.assumptions);
        
    if constexpr (std::is_same_v<SolutionProcessor, GenericSolutionProcessor>)
        processor_.cb = opts.solution_callback; // take the pointer
    
}

template <typename SolutionProcessor>
ExhaustiveSearch<SolutionProcessor>::ExhaustiveSearch(CaDiCaL::Solver * s) : ExhaustiveSearch(s, {}, {}) { }

template <typename SolutionProcessor>
ExhaustiveSearch<SolutionProcessor>::~ExhaustiveSearch () {
    if (!observed.empty())
        solver->disconnect_external_propagator ();
    //std::cout << "c Number of solutions: " << sol_count << " (" << global_sol_count << ")" << std::endl;
}

template <typename SolutionProcessor>
void ExhaustiveSearch<SolutionProcessor>::notify_assignment(const std::vector<int>& lits) {
    for (int lit : lits) { // Track assignments of observed variables
        int idx = abs(lit) - 1;
        if (assignment[idx] == 0) { // Variable not yet assigned
            assignment[idx] = lit; // Store the signed literal
            assigned_count++; // Increment total assigned variables
            assignments_by_level.back().push_back(lit); // Store when this literal was assigned

            int req = assumption_lit_[idx];
            if (req != 0 && lit != req)
                violated_assumptions_++;
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

            int req = assumption_lit_[idx];
            if (req != 0 && lit != req)
                violated_assumptions_--;
        }
        assignments_by_level.pop_back(); // Remove history from list
    }
}

template <typename SolutionProcessor>
void ExhaustiveSearch<SolutionProcessor>::block_partial_solution() {
    if (violated_assumptions_ > 0)
        return;

    clause_buf_.clear();
    pos_vars_buf_.clear();
    
    for (int var : observed) {
        int lit = assignment[var - 1];

        if (lit == 0)
            continue;
        if (lit > 0)
            pos_vars_buf_.push_back(var);
        if (lit > 0 || !only_neg)
            clause_buf_.push_back(-lit);
    }

    static constexpr uint64_t kHashSeed = 0x517cc1b727220a95ULL;
    uint64_t h = can_forget ? es_wyhash(pos_vars_buf_.data(), pos_vars_buf_.size() * sizeof(int), kHashSeed) : 0; // wyhash the raw bytes of the pos_vars vector (order is deterministic: observed order).

    bool is_new = !can_forget || seen_hashes.insert(h).second; // Duplication check
    
    if (is_new) { // Is unique solution so we record it
        sol_count++;
        global_sol_count++;
        solver->set_num_sol(sol_count);

        // Write to file (always a complete line) and/or console (if output_solutions)
        if (solfile) {
            for (int var : pos_vars_buf_)
                fprintf(solfile, "%d ", var);
            fputs("0\n", solfile);
        }
        if (output_solutions) {
            std::cout << "c New solution: ";
            for (int var : pos_vars_buf_)
                std::cout << var << " ";
            std::cout << "0\n";
        }

        if(processor_)
            processor_(pos_vars_buf_);

        if (track_solutions)
            solutions.push_back(pos_vars_buf_);
    }

    pending_pos_ = clause_buf_.size();
    solver->add_trusted_clause(clause_buf_);
}

template <typename SolutionProcessor>
bool ExhaustiveSearch<SolutionProcessor>::cb_has_external_clause (bool& is_forgettable) {
    is_forgettable = can_forget;
    if (assigned_count == observed.size())
        block_partial_solution();
    return pending_pos_ > 0;
}

template <typename SolutionProcessor>
int ExhaustiveSearch<SolutionProcessor>::cb_add_external_clause_lit () {
    if (pending_pos_ > 0)
        return clause_buf_[--pending_pos_];
    return 0;
}

template <typename SolutionProcessor>
void ExhaustiveSearch<SolutionProcessor>::set_assumptions(const std::vector<int>& assumptions) {
    assumptions_.clear();
    assumption_lit_.assign(is_observed_.size(), 0); // reset
    violated_assumptions_ = 0;

    for (int lit : assumptions) {
        int idx = abs(lit) - 1;
        if (idx < (int)is_observed_.size() && is_observed_[idx]) {
            assumptions_.push_back(lit);
            assumption_lit_[idx] = lit; 
        }
    }
    clear_solutions();
}