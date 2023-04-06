#include "iterative_deepening_unrolled.h"

check_result iterative_deepening_unrolled::solve(const expr& e) {
    while(true) {
        m_worlds.push_back(fresh_world_constant());
        LOG("Trying size " << domain_size() << "...");

        LOG("translation...");
        // clear cache
        // old entries are always invalid because they do not consider new worlds beneath them
        m_cache.clear();
        for(unsigned world = 0; world < domain_size(); world++)
            m_cache.push_back(std::unordered_map<unsigned, expr>());

        // wlog: start world is first world
        // no point in caching it though
        expr translation = unroll(e, 0);

        LOG("solving...");
        m_solver.push();
        m_solver.add(translation);
        // worlds are disjoint: not strictly necessary but much faster
        m_solver.add(distinct(m_worlds));
        if(m_solver.check() == sat)
            return sat;
        LOG("...done, go again.");
        m_solver.pop();
    }
}

// TODO non-recursive version
expr iterative_deepening_unrolled::unroll(const expr &e, unsigned world) {
    if(e.is_app()) {
        const func_decl &decl = e.decl();
        if(is_placeholder(decl))
            return m_worlds[world];
        else if(is_modal(decl)) {
            const expr &relation = e.arg(0);
            expr_vector children(m_ctx);
            const expr &subexpr = e.arg(1);
            for(unsigned next = 0; next < domain_size(); next++) {
                expr reachable = m_reachable(relation, m_worlds[world], m_worlds[next]);
                expr unrolled_subexpr = unroll_and_cache(subexpr, next);
                children.push_back(is_box(decl)
                    ? implies(reachable, unrolled_subexpr)
                    : reachable && unrolled_subexpr
                );
            }
            return is_box(decl)
                ? mk_and(children)
                : mk_or(children);
        }
        else {
            expr_vector args(m_ctx);
            for(unsigned i = 0; i < e.num_args(); i++)
                args.push_back(unroll_and_cache(e.arg(i), world));
            return decl(args);
        }
    }
    else {
        std::cerr << e << std::endl;
        assert(false);
    }
}

expr iterative_deepening_unrolled::unroll_and_cache(const expr &e, unsigned world) {
    std::unordered_map<unsigned, expr> &cache = m_cache[world];
    if(auto found = cache.find(e.id()); found != cache.end())
        return found->second;

    expr unrolled = unroll(e, world);
    cache.insert({e.id(), unrolled});
    return unrolled;
}
