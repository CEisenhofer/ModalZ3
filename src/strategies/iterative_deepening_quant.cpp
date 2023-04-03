#include "iterative_deepening_quant.h"

check_result iterative_deepening_quant::solve(const expr& e) {

    expr x = fresh_world_constant();
    expr world = fresh_world_constant();
    expr constraint = world == x;
    m_solver.add(e);

    for (unsigned num_worlds = 1;; num_worlds++) {
        LOG("Trying size " << num_worlds << "...");
        expr_vector assumptions(ctx());
        assumptions.push_back(forall(x, constraint));
        if (m_solver.check(assumptions) == sat) {
             return sat;
        }

        expr_vector core = m_solver.unsat_core();
        if (core.empty())
            return unsat; // the assumption is not contained (there is only one; if it is not empty it is the cardinality constraint)

        std::string name("w");
        name += std::to_string(num_worlds);
        expr brave_new = fresh_world_constant();
        constraint = constraint || x == brave_new;
    }
}
