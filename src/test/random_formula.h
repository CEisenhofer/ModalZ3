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
    std::uniform_int_distribution<unsigned> m_expr_gen;
    std::weibull_distribution<double> m_arg_cnt_gen;
    std::uniform_int_distribution<unsigned> m_general_gen;
    std::bernoulli_distribution m_new_var_gen;

    const z3::sort m_world_sort, m_relation_sort;
    const z3::func_decl m_dia, m_box;
    const z3::expr m_placeholder;
    
    expr_vector m_relations;
    
    unsigned m_max_depth;
    
    decltype(m_cases) create_cases(random_formula* f);
    unsigned sum_cases();
    
    void init_generator();
    
    expr get_subexpr(std::vector<func_decl>& vars, unsigned depth);
    
public:
    
    random_formula(context& ctx, unsigned relation_cnt, z3::sort world_sort, z3::sort relation_sort, z3::func_decl dia, z3::func_decl box, z3::expr placeholder) : random_formula(ctx, (unsigned)time(nullptr), relation_cnt, world_sort, relation_sort, dia, box, placeholder) {}
    random_formula(context& ctx, unsigned seed, unsigned relation_cnt, z3::sort world_sort, z3::sort relation_sort, z3::func_decl dia, z3::func_decl box, z3::expr placeholder);
    
    void set_max_depth(unsigned max) {
        m_max_depth = max;
    }
    
    unsigned get_last_seed() const {
        return m_last_seed;
    }
    
    expr get();
    

};
