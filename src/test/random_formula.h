#pragma once
#include <random>
#include "strategy.h"
#include "z3++.h"

using namespace z3;

struct expr_not_hash {
    size_t operator()(const z3::expr& e) const {
        return e.is_not() ? e.arg(0).hash() : e.hash();
    }
};
struct expr_not_eq {
    bool operator()(const z3::expr& e1, const z3::expr& e2) const {
        expr f1 = e1.is_not() ? e1.arg(0) : e1;
        expr f2 = e2.is_not() ? e2.arg(0) : e2;
        return eq(f1, f2);
    }
};

class random_formula {

    unsigned m_last_seed = 0;
    unsigned m_current_seed = 0;
    context& m_ctx;
    
    std::vector<std::tuple<unsigned, unsigned, std::function<expr(random_formula&, std::vector<func_decl>&, unsigned d)>>> m_cases;
    
    std::mt19937 m_mt;
    std::uniform_int_distribution<unsigned> m_expr_gen;
    std::weibull_distribution<double> m_arg_cnt_gen;
    std::uniform_int_distribution<unsigned> m_general_gen;
    std::bernoulli_distribution m_new_var_gen;

    const modal_decls& m_decls;
    
    expr_vector m_relations;
    
    unsigned m_max_depth;
    bool m_simplified; // the simplifier will not really be able to simplify a lot if this is true
    
    decltype(m_cases) create_cases(random_formula* f);
    unsigned sum_cases();
    
    void init_generator();
    
    expr get_subexpr(std::vector<func_decl>& vars, unsigned depth);
    expr get_subexpr(std::vector<func_decl>& vars, unsigned depth, std::unordered_set<expr, expr_not_hash, expr_not_eq>& already);
    
public:
    
    random_formula(context& ctx, const modal_decls& decls, unsigned relation_cnt, bool simplified) : random_formula(ctx, decls, (unsigned)time(nullptr), relation_cnt, simplified) {}
    random_formula(context& ctx, const modal_decls& decls, unsigned seed, unsigned relation_cnt, bool prevent_collaps);
    
    void set_max_depth(unsigned max) {
        m_max_depth = max;
    }
    
    unsigned get_last_seed() const {
        return m_last_seed;
    }
    
    expr get();
    

};
