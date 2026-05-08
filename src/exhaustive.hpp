#include "internal.hpp"
#include <deque>
#include <vector>
#include <cstdint>
#include <cstring>
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
class ExhaustiveSearch : CaDiCaL::ExternalPropagator {
    CaDiCaL::Solver* solver;
    std::vector<std::vector<int>> new_clauses;
    std::vector<int> assignment;
    std::deque<std::vector<int>> assignments_by_level;

    size_t assigned_count = 0;
    
    std::vector<int> observed;
    bool can_forget = false;
    bool track_solutions = false;
    bool only_neg = false;
    long sol_count = 0;
    
    FILE * solfile;

    std::vector<std::vector<int>> solutions;
    
    // Deduplication: wyhash of the set of positive variables in the solution
    std::unordered_set<uint64_t> seen_hashes;
    
public:
    ExhaustiveSearch(CaDiCaL::Solver * s, std::vector<int> to_observe, bool only_neg, FILE * solfile, bool can_forget, bool track_solutions);
    ~ExhaustiveSearch ();
    void notify_assignment(const std::vector<int>& lits);
    void notify_new_decision_level ();
    void notify_backtrack (size_t new_level);
    bool cb_check_found_model (const std::vector<int> & model);
    bool cb_has_external_clause (bool& is_forgettable);
    int cb_add_external_clause_lit ();
    int cb_decide ();
    int cb_propagate ();
    int cb_add_reason_clause_lit (int plit);
    long get_solution_count() const { return sol_count; }
    const std::vector<std::vector<int>>& get_solutions() const { return solutions; }
    void clear_solutions() { solutions.clear(); sol_count = 0; seen_hashes.clear(); }

private:
    void block_partial_solution();
};