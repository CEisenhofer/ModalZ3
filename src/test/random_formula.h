#pragma once
#include <random>
#include "z3++.h"

using namespace z3;

class random_formula {
    
    
    unsigned m_last_seed = 0;
    unsigned m_current_seed = 0;
    context& m_ctx;
    
    std::vector<std::tuple<unsigned, unsigned, std::function<expr(random_formula&, std::vector<func_decl>&, unsigned d)>>> m_cases;
    
    std::mt19937 m_mt;
    const std::uniform_int_distribution<unsigned> m_expr_gen;
    const std::weibull_distribution<double> m_arg_cnt_gen;
    const std::uniform_int_distribution<unsigned> m_general_gen;
    const std::bernoulli_distribution m_new_var_gen;
    
    unsigned m_max_depth;
    
    decltype(m_cases) create_cases(random_formula* f);
    unsigned sum_cases();
    
    void init_generator();
    
    expr get_subexpr(std::vector<func_decl>& vars, unsigned depth);
    
public:
    
    random_formula(context& ctx) : random_formula(ctx, (unsigned)time(nullptr)) { }
    random_formula(context& ctx, unsigned seed);
    
    void set_max_depth(unsigned max) {
        m_max_depth = max;
    }
    
    unsigned get_last_seed() const {
        return m_last_seed;
    }
    
    expr get();
    

};
