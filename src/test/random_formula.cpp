#include "assertion.h"
#include "random_formula.h"

decltype(random_formula::m_cases) random_formula::create_cases(random_formula* f) {
    decltype(random_formula::m_cases) v;
    // prop. occ.; mean args; generation-fct
    v.emplace_back(1, 0, [](random_formula& f, std::vector<func_decl>& v, unsigned d) { return f.m_ctx.bool_val(false); });
    v.emplace_back(1, 0, [](random_formula& f, std::vector<func_decl>& v, unsigned d) { return f.m_ctx.bool_val(true); });
    v.emplace_back(2, 3, [](random_formula& f, std::vector<func_decl>& v, unsigned d) {
        expr_vector args(f.m_ctx);
        unsigned cnt = (unsigned)f.m_arg_cnt_gen(f.m_mt);
        if (cnt == 0)
            cnt = 1;
        for (unsigned i = 0; i < cnt; i++)
            args.push_back(f.get_subexpr(v, d));
        
        return mk_and(args); 
    });
    v.emplace_back(2, 3, [](random_formula& f, std::vector<func_decl>& v, unsigned d) {
        expr_vector args(f.m_ctx);
        unsigned cnt = (unsigned)f.m_arg_cnt_gen(f.m_mt);
        if (cnt == 0)
            cnt = 1;
        for (unsigned i = 0; i < cnt; i++)
            args.push_back(f.get_subexpr(v, d));
        
        return mk_or(args); 
    });
    v.emplace_back(1, 2, [](random_formula& f, std::vector<func_decl>& v, unsigned d) { return implies(f.get_subexpr(v, d), f.get_subexpr(v, d)); });
    v.emplace_back(3, 2, [](random_formula& f, std::vector<func_decl>& v, unsigned d) { return !f.get_subexpr(v, d); });
    v.emplace_back(3, 1, [](random_formula& f, std::vector<func_decl>& v, unsigned d) { return f.m_decls.dia(f.m_relations[f.m_general_gen(f.m_mt) % f.m_relations.size()], f.get_subexpr(v, d)); });
    v.emplace_back(3, 1, [](random_formula& f, std::vector<func_decl>& v, unsigned d) { return f.m_decls.box(f.m_relations[f.m_general_gen(f.m_mt) % f.m_relations.size()], f.get_subexpr(v, d)); });
    v.emplace_back(5, 0, [](random_formula& f, std::vector<func_decl>& v, unsigned d) {
        if (!v.empty() && f.m_new_var_gen(f.m_mt)) {
            return v[(f.m_general_gen(f.m_mt) % v.size())](f.m_decls.placeholder());
        }
        else {
            Z3_sort domain_sort = f.m_decls.world_sort;
            func_decl func(f.m_ctx, Z3_mk_fresh_func_decl(f.m_ctx, "Var", 1, &domain_sort, f.m_ctx.bool_sort()));
            v.push_back(func);
            return func(f.m_decls.placeholder());
        }
    });

    return v;
}

unsigned random_formula::sum_cases() {
    unsigned total = 0;
    for (const auto& m_case : m_cases)
        total += std::get<0>(m_case);
    return total;
}

random_formula::random_formula(context& ctx, const modal_decls& decls, unsigned seed, unsigned relation_cnt) :
    m_ctx(ctx), m_last_seed(seed), m_current_seed(seed),
    m_cases(create_cases(this)),
    m_mt(seed),
    m_general_gen(),
    m_expr_gen(0, sum_cases() - 1),
    m_arg_cnt_gen(1, 3), // Mean: 3
    m_new_var_gen(0.5),
    m_decls(decls),
    m_relations(ctx),
    m_max_depth(6)
    {
    
    SASSERT(relation_cnt > 0);
    for (unsigned i = 0; i < relation_cnt; i++) {
        m_relations.push_back(ctx.constant(("r" + std::to_string(i + 1)).c_str(), m_decls.relation_sort));
    }
}

void random_formula::init_generator() {
    m_mt = std::mt19937(m_current_seed);
    m_last_seed = m_current_seed;
    m_current_seed = m_general_gen(m_mt);
}

expr random_formula::get() {
    init_generator();
    
    std::vector<func_decl> vars;
    expr e = get_subexpr(vars, 0);
    
    return e;
}
expr random_formula::get_subexpr(std::vector<func_decl>& vars, unsigned depth){
    expr e(m_ctx);
repeat:
    unsigned selection = m_expr_gen(m_mt);
    unsigned sum = 0;
    unsigned i = 0;
    for (; i < m_cases.size() - 1; i++) {
        sum += std::get<0>(m_cases[i]);
        if (sum > selection) {
            if (depth > m_max_depth && std::get<1>(m_cases[i]) > 0)
                goto repeat;
            e = std::get<2>(m_cases[i])(*this, vars, depth + 1);
            break;
        } 
    }
    if (i == m_cases.size() - 1)
        e = std::get<2>(m_cases[i])(*this, vars, depth + 1);
    
    return e;
}
