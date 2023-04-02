#pragma once
#include <random>
#include "strategy.h"
#include "z3++.h"

using namespace z3;

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
    
    decltype(m_cases) create_cases(random_formula* f);
    unsigned sum_cases();
    
    void init_generator();
    
    expr get_subexpr(std::vector<func_decl>& vars, unsigned depth);
    
public:
    
    random_formula(context& ctx, const modal_decls& decls, unsigned relation_cnt) : random_formula(ctx, decls, (unsigned)time(nullptr), relation_cnt) {}
    random_formula(context& ctx, const modal_decls& decls, unsigned seed, unsigned relation_cnt);
    
    void set_max_depth(unsigned max) {
        m_max_depth = max;
    }
    
    unsigned get_last_seed() const {
        return m_last_seed;
    }
    
    expr get();
    

};
