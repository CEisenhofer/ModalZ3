#pragma once

#include <unordered_set>
#include <z3++.h>

#include "standard_translation.h"

using namespace z3;

class iterative_deepening_unrolled : public strategy {
public:
    iterative_deepening_unrolled(context& ctx, const modal_decls& decls) :
        strategy(ctx, decls),
        m_worlds(ctx),
        m_reachable(ctx.function(
         "reachable",
         decls.relation_sort,
         decls.world_sort,
         decls.world_sort,
         ctx.bool_sort()
        ))
    {}

    // trivial overrides
    virtual expr create_formula(const expr &e) override { return e; }
    virtual unsigned domain_size() override { return m_worlds.size(); }
    virtual void output_model(const model &model, std::ostream &out) override {
        out << model;
    }

    check_result solve(const expr& e) override;

protected:
    std::vector<std::unordered_map<unsigned, expr>> m_cache;
    expr_vector m_worlds;
    func_decl m_reachable;
    expr unroll(const expr &expr, unsigned world);
    expr unroll_and_cache(const expr &expr, unsigned world);
};
