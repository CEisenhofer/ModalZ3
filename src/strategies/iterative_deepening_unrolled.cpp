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

        m_solver.push();

        // wlog: start world is first world
        // no point in caching it though
        m_solver.add(unroll(e, 0));

        // worlds are disjoint: not strictly necessary but much faster
        m_solver.add(distinct(m_worlds));

        for(const expr &named : m_named_worlds) {
            expr_vector named_worlds(m_ctx);
            for(unsigned world = 0; world < domain_size(); world++)
                named_worlds.push_back(named == m_worlds[world]);
            m_solver.add(mk_or(named_worlds));
        }

        LOG("solving...");
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
        else if(is_global(decl)) {
            expr_vector children(m_ctx);
            const expr &subexpr = e.arg(0);
            for(unsigned world = 0; world < domain_size(); world++)
                children.push_back(unroll_and_cache(subexpr, world));
            return mk_and(children);
        }
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
            if(domain_size() == 1 && decl.range().id() == get_world_sort().id() && !m_named_world_ids.contains(e.id())) {
                m_named_world_ids.insert(e.id());
                m_named_worlds.push_back(e);
            }
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
