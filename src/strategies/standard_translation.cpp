#include <stack>

#include "standard_translation.h"
#include "assertion.h"
#include "parse_exception.h"

standard_translation::standard_translation(context& ctx, const modal_decls& decls) :
            strategy(ctx, decls), m_variables(ctx), m_reachable(ctx.function("reachable", decls.relation_sort, decls.world_sort, decls.world_sort, ctx.bool_sort())) {
    m_variables.push_back(fresh_world_constant());
}

expr standard_translation::create_formula(const expr& e) {
    std::stack<expr_info> expr_to_process;
    expr_info info(e);
    info.top_level = true;
    info.no_scope = true;

    expr_to_process.push(info);

    SASSERT(m_processed_args.empty());
    SASSERT(m_apply_list.empty());
    m_processed_args.push({});

    while (!expr_to_process.empty()) {
        expr_info current = expr_to_process.top();
        expr_to_process.pop();

        VERIFY(current.e.is_app());
        LOG("Parsing (2): " << current.e);
        
        if (is_modal(current.decl) || is_global(current.decl)) {
            LOG("Adding variable for " << current.e);
            m_variables.push_back(fresh_world_constant());
        }

        for (unsigned i = current.e.num_args(); i > 0; i--) {
            expr_info info2(current.e.arg(i - 1));
            info2.top_level = current.top_level && current.decl.decl_kind() == Z3_OP_AND;
            info2.no_scope = current.no_scope && !is_ml_interpreted(current.decl);
            expr_to_process.push(info2);
        }

        m_apply_list.push(current);
        m_processed_args.push({});

        while (!m_apply_list.empty() && (m_apply_list.top().arity <= m_processed_args.top().size())) {
            current = m_apply_list.top();
            m_apply_list.pop();
            expr_vector args(m_ctx);

            LOG("Processing (2) " << current.decl.name() << " / " << current.arity << (current.arity > 0 ? " with" : ""));
            for (unsigned i = 0; i < current.arity; i++) {
                args.push_back(m_processed_args.top()[i]);
                LOG("\t" << args.back());
            }
            m_processed_args.pop();

            if (current.decl.decl_kind() == Z3_OP_UNINTERPRETED) {
                if (is_modal(current.decl)) { // Modal operator
                    expr relation = current.e.arg(0);
                    if (!relation.is_const())
                        throw parse_exception("Relations have to be constants unlike " + relation.to_string());
                    if (!m_relation_to_id.contains(relation.decl())) {
                        m_relation_to_id[relation.decl()] = m_relation_to_id.size();
                        m_relation_list.push_back(relation.decl());
                    }

                    SASSERT(eq(current.decl, m_decls.box));
                    
                    expr new_world = m_variables.back();
                    m_variables.pop_back();
                    expr old_world = m_variables.back();
                    expr forall = z3::forall(new_world, implies(m_reachable(args[0], old_world, new_world), args[1]));
                    LOG("Created: " << forall);
                    m_processed_args.top().push_back(forall);
                }
                else if (is_global(current.decl)) {
                    if (!current.top_level)
                        throw parse_exception("\"global\" may only occur top-level: " + current.e);
                    expr new_world = m_variables.back();
                    m_variables.pop_back();
                    expr forall = z3::forall(new_world, args[0]);
                    LOG("Created: " << forall);
                    m_processed_args.top().push_back(forall);
                }
                else if (is_trans(current.decl)) {
                    if (!current.top_level)
                        throw parse_exception("\"trans\" may only occur top-level: " + current.e);
                    expr new_world = m_variables.back();
                    expr relation = current.e.arg(0);
                    expr x = expr(m_ctx, Z3_mk_fresh_const(m_ctx, "var", m_decls.world_sort));
                    expr y = expr(m_ctx, Z3_mk_fresh_const(m_ctx, "var", m_decls.world_sort));
                    expr z = expr(m_ctx, Z3_mk_fresh_const(m_ctx, "var", m_decls.world_sort));

                    expr forall = z3::forall(x, y, z,
                                             implies(m_decls.reachable(relation, x, y) & m_decls.reachable(relation, y, z), m_decls.reachable(relation, x, z)));
                    LOG("Created: " << forall);
                    m_processed_args.top().push_back(forall);
                }
                else { // we attach the world sort
                    sort_vector domain(m_ctx);
                    for (const z3::expr& arg : args)
                        domain.push_back(arg.get_sort());
                    if (!args.empty() && z3::eq(args[0].get_sort(), m_decls.world_sort)) {
                        if (z3::eq(args[0].decl(), m_decls.placeholder)) {
                            z3::expr x = m_variables.back();
                            args.set(0, x);
                            // throw parse_exception("Currently not supporting ABox/complex world terms: " + args.to_string());
                        }
                    }

                    func_decl new_func = m_ctx.function(current.decl.name(), domain, current.decl.range());
                    m_processed_args.top().push_back(new_func(args));
                    if (!m_uf_to_id.contains(current.decl)) {
                        m_uf_list.push_back(current.decl);
                        m_uf_to_id[current.decl] = m_uf_to_id.size();
                    }
                }
            }
            else
                m_processed_args.top().push_back(current.decl(args));
        }
    }

    VERIFY(m_variables.size() == 1);
    VERIFY(m_processed_args.size() == 1);
    if (m_processed_args.top().size() != 1) {
        for (unsigned i = 0; i < m_processed_args.top().size(); i++) {
            LOG("\tInvalid element: " << m_processed_args.top()[i]);
        }
    }
    VERIFY(m_processed_args.top().size() == 1);
    VERIFY(m_apply_list.empty());
    expr ret = m_processed_args.top()[0];
    m_processed_args.pop();
    return ret;
}

void standard_translation::output_model(const model& model, std::ostream& ostream) {
    // LOG("Native model: " << model);
    Z3_ast_vector domain_native = Z3_model_get_sort_universe(m_ctx, model, m_decls.world_sort);
    if (domain_native == nullptr) {
        for (const auto& r : m_relation_list) {
            ostream << "Relation " << r.name().str() << ":\n";
        }
        for (const auto& uf : m_uf_list) {
            if (uf.is_const() && (eq(uf.range(), m_decls.relation_sort) || eq(uf.range(), m_decls.world_sort)))
                continue;
            ostream << uf.name().str().c_str() << ":\n";
        }
        return;
    }
    
    expr_vector domain = expr_vector(m_ctx, domain_native);
    for (const auto& r : m_relation_list) {
        ostream << "Relation " << r.name().str() << ":\n";
        unsigned w1i = (unsigned)-1;
        for (const auto& w1 : domain) {
            unsigned w2i = (unsigned)-1;
            w1i++;
            unsigned output_cnt = 0;
            for (const auto& w2 : domain) {
                w2i++;
                if (!model.eval(m_reachable(r(), w1, w2), true).is_true())
                    continue;
                output_cnt++;
                ostream << "\tw" << w1i << " -> w" << w2i << "\n"; 
            }
            if (output_cnt > 0)
                ostream << "\n";
        }
    }
    
    for (const auto& uf : m_uf_list) {
        if (uf.is_const() && (eq(uf.range(), m_decls.relation_sort) || eq(uf.range(), m_decls.world_sort)))
            continue;
        ostream << uf.name().str().c_str() << ":\n";
        if (uf.arity() != 1 || !eq(uf.domain(0), m_decls.world_sort)) {
            ostream << "\tSkipped because of complexity\n";
        }
        else {
            unsigned wi = 0;
            for (const auto& w : domain) {
                expr eval = model.eval(uf(w), true);
                ostream << "\tw" << ++wi << ": " << eval << "\n";
            }
        }
        ostream << "\n";
    }
}

unsigned standard_translation::domain_size() {
    z3::model model = m_solver.get_model();
    Z3_ast_vector domain_native = Z3_model_get_sort_universe(m_ctx, model, m_decls.world_sort);
    if (domain_native == nullptr)
        return 1; // TODO: Bug in Z3?
        
    expr_vector domain = expr_vector(m_ctx, domain_native);
    return domain.size();
}
