#include "exhaustive.hpp"
#include <iostream>
#include <deque>
#include <cassert>

ExhaustiveSearch::ExhaustiveSearch(CaDiCaL::Solver * s, const ExhaustiveSearchOptions& opts) : solver(s), solfile(opts.solfile), only_neg(opts.only_neg), 
        can_forget(opts.can_forget), track_solutions(opts.track_solutions), output_solutions(opts.output_solutions), solution_callback(opts.solution_callback) {
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
}

ExhaustiveSearch::ExhaustiveSearch(CaDiCaL::Solver * s) : ExhaustiveSearch(s, {}) { }

ExhaustiveSearch::~ExhaustiveSearch () {
    if (!observed.empty())
        solver->disconnect_external_propagator ();
        //std::cout << "c Number of solutions: " << sol_count << std::endl;
}

void ExhaustiveSearch::notify_assignment(const std::vector<int>& lits) {
    for (int lit : lits) { // Track assignments of observed variables
        int idx = abs(lit) - 1;
        if (assignment[idx] == 0) { // Variable not yet assigned
            assignment[idx] = lit; // Store the signed literal
            assigned_count++; // Increment total assigned variables
            assignments_by_level.back().push_back(lit); // Store when this literal was assigned
        }
    }    
}

void ExhaustiveSearch::notify_new_decision_level () {
    assignments_by_level.push_back({}); // Add new vector to track history
}

void ExhaustiveSearch::notify_backtrack (size_t new_level) {
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

void ExhaustiveSearch::block_partial_solution() {
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

        if(solution_callback)
            solution_callback(pos_vars);

        if (track_solutions)
            solutions.push_back(std::move(pos_vars));
    }

    new_clauses.push_back(std::move(clause)); // Always add the blocking clause regardless of duplication, otherwise the solver would find the same assignment again
    solver->add_trusted_clause(new_clauses.back());
}

bool ExhaustiveSearch::cb_has_external_clause (bool& is_forgettable) {
    is_forgettable = can_forget;
    if (assigned_count == observed.size()) // Found all assignments and no solution found
        block_partial_solution();
    else
        return false;

    return true;
}

int ExhaustiveSearch::cb_add_external_clause_lit () {
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