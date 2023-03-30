#include <stack>

#include "standard_translation.h"
#include "assertion.h"
#include "parse_exception.h"

standard_translation::standard_translation(context& ctx, const sort& world_sort, const sort& reachability_sort, const func_decl& dia, const func_decl& box, const func_decl& reachable, const expr& placeholder) :
            strategy(ctx, world_sort, reachability_sort, dia, box, reachable, placeholder), m_variables(ctx) {
    m_variables.push_back(fresh_world_constant());
}

expr standard_translation::create_formula(const expr& e) {
    std::stack<expr_info> expr_to_process;
    expr_info info(e);
    expr_to_process.push(info);

    SASSERT(m_processed_args.empty());
    SASSERT(m_apply_list.empty());
    m_processed_args.push({});

    while (!expr_to_process.empty()) {
        expr_info current = expr_to_process.top();
        expr_to_process.pop();

        VERIFY(current.e.is_app());
        LOG("Parsing (2): " << current.e);
        
        if (is_modal(current.decl)) 
            m_variables.push_back(fresh_world_constant());

        for (unsigned i = current.e.num_args(); i > 0; i--) {
            expr_info info2(current.e.arg(i - 1));
            expr_to_process.push(info2);
        }

        m_apply_list.push(current);
        m_processed_args.push({});

        while (!m_apply_list.empty() && (m_apply_list.top().arity <= m_processed_args.top().size())) {
            expr_info app = m_apply_list.top();
            m_apply_list.pop();
            expr_vector args(m_ctx);

            LOG("Processing (2) " << app.decl.name() << " / " << app.arity << (app.arity > 0 ? " with" : ""));
            for (unsigned i = 0; i < app.arity; i++) {
                args.push_back(m_processed_args.top()[i]);
                LOG("\t" << args.back());
            }
            m_processed_args.pop();

            if (app.decl.decl_kind() == Z3_OP_UNINTERPRETED) {
                if (is_modal(app.decl)) { // Modal operator
                    expr relation = app.e.arg(0);
                    if (!relation.is_const())
                        throw parse_exception("Relations have to be constants unlike " + relation.to_string());
                    if (!m_relation_to_id.contains(relation.decl())) {
                        m_relation_to_id[relation.decl()] = m_relation_to_id.size();
                        m_relation_list.push_back(relation.decl());
                    }

                    SASSERT(eq(app.decl, m_box_decl));
                    
                    expr new_world = m_variables.back();
                    m_variables.pop_back();
                    expr old_world = m_variables.back();
                    expr forall = z3::forall(new_world, implies(m_reachable_decl(args[0], old_world, new_world), args[1]));
                    LOG("Created: " << forall);
                    m_processed_args.top().push_back(forall);
                }
                else { // we attach the world sort
                    sort_vector domain(m_ctx);
                    for (const z3::expr& arg : args)
                        domain.push_back(arg.get_sort());
                    if (!args.empty() && z3::eq(args[0].get_sort(), m_world_sort)) {
                        if (!z3::eq(args[0], m_placeholder))
                            throw parse_exception("Currently not supporting ABox/complex world terms: " + args.to_string());
                        z3::expr x = m_variables.back();
                        args.set(0, x);
                    }

                    func_decl new_func = m_ctx.function(app.decl.name(), domain, app.decl.range());
                    m_processed_args.top().push_back(new_func(args));
                    if (!m_uf_to_id.contains(app.decl)) {
                        m_uf_list.push_back(app.decl);
                        m_uf_to_id[app.decl] = m_uf_to_id.size();
                    }
                }
            }
            else
                m_processed_args.top().push_back(app.decl(args));
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
    expr_vector domain = expr_vector(m_ctx, Z3_model_get_sort_universe(m_ctx, model, m_world_sort));
    for (const auto& r : m_relation_list) {
        ostream << "Relation " << r.name().str() << ":\n";
        unsigned w1i = 0; 
        for (const auto& w1 : domain) {
            unsigned w2i = 0;
            w1i++;
            unsigned output_cnt = 0;
            for (const auto& w2 : domain) {
                w2i++;
                if (!model.eval(m_reachable_decl(r(), w1, w2), true).is_true())
                    continue;
                output_cnt++;
                ostream << "\tw" << w1i << " -> w" << w2i << "\n"; 
            }
            if (output_cnt > 0)
                ostream << "\n";
        }
    }
    
    for (const auto& uf : m_uf_list) {
        if (uf.is_const() && (eq(uf.range(), m_reachability_sort) || eq(uf.range(), m_world_sort)))
            continue;
        ostream << uf.name().str().c_str() << ":\n";
        if (uf.arity() != 1 || !eq(uf.domain(0), m_world_sort)) {
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
