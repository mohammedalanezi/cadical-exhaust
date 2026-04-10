#include "exhaustive.hpp"
#include <iostream>
#include <deque>
#include <cassert>

ExhaustiveSearch::ExhaustiveSearch(CaDiCaL::Solver * s, std::vector<int> to_observe, bool only_neg, FILE * solfile, bool can_forget, bool track_solutions) : solver(s) {
    if (to_observe.empty())
    { // No order provided; run exhaustive search on all variables
        observed.reserve(s->vars());
        for(int i=0; i < s->vars(); i++)
            observed.push_back(i+1);
    }
    else 
        observed = to_observe;

    this->only_neg = only_neg;
    this->track_solutions = track_solutions;
    this->solfile = solfile;
    this->can_forget = can_forget;
    
    assignment.assign(s->vars(), 0);
    assignments_by_level.push_back({});
    
    solver->connect_external_propagator(this);
    
    //std::cout << "c Running exhaustive search on " << observed.size() << " variables" << std::endl;
    
    for (int var : observed)
        solver->add_observed_var(var);
}

ExhaustiveSearch::~ExhaustiveSearch () {
    if (!observed.empty()) {
        solver->disconnect_external_propagator ();
        //std::cout << "c Number of solutions: " << sol_count << std::endl;
    }
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
    sol_count++;
    solver->set_num_sol(sol_count);

#ifdef VERBOSE
    if (!solfile)
      std::cout << "c New solution: ";
#endif

    std::vector<int> clause;
    std::vector<int> sol_vars; 
    clause.reserve(observed.size() + 1);
    if (track_solutions) 
        sol_vars.reserve(observed.size());
    
    for (int j = 0; j < observed.size(); j++) {
        int var = observed[j];
        int lit = assignment[var - 1];

        if(lit==0)
            continue;
        else if(track_solutions && lit > 0)
            sol_vars.push_back(var);
        
#ifdef VERBOSE
        if (lit > 0) {
            if(!solfile)
              std::cout << var << " ";
            else
              fprintf(solfile, "%d ", var);
        }
#endif
        if (lit > 0 || !only_neg)
            clause.push_back(-lit);
    }
    
#ifdef VERBOSE
    if(!solfile) 
        std::cout << "0" << std::endl;
    else 
        fprintf(solfile, "0\n");
#endif

    new_clauses.push_back(clause);
    solver->add_trusted_clause(clause);
    if(track_solutions)
        solutions.push_back(std::move(sol_vars));
}

bool ExhaustiveSearch::cb_check_found_model (const std::vector<int> & model) {
    (void)model;
    return false;
}

bool ExhaustiveSearch::cb_has_external_clause (bool& is_forgettable) {
    is_forgettable = can_forget;
    if (assigned_count == observed.size()) { // Found all assignments and no solution found
        block_partial_solution();
    }
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

int ExhaustiveSearch::cb_decide () { return 0; }
int ExhaustiveSearch::cb_propagate () { return 0; }
int ExhaustiveSearch::cb_add_reason_clause_lit (int plit) {
    (void)plit;
    return 0;
}