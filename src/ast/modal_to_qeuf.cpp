#include <stack>

#include "modal_to_qeuf.h"
#include "assertion.h"

expr modal_to_qeuf::get_world(unsigned id) {
    if (id < m_world_variables.size()) 
        return m_world_variables[id];
    else {
        for (unsigned i = m_world_variables.size(); i <= id; i++) 
            m_world_variables.push_back({ m_ctx, Z3_mk_fresh_const(m_ctx, "World", m_world_sort) });
        return m_world_variables[id];
    }
}

modal_to_qeuf::modal_to_qeuf(context& ctx) : 
        modal_to_euf_base(ctx),
        m_world_variables(ctx) { }

expr modal_to_qeuf::create_formula(const expr& e) {
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

        for (unsigned i = current.e.num_args(); i > 0; i--) {
            expr_info info2(current.e.arg(i - 1));
            info2.world = current.world;
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

            if (current.decl.decl_kind() == Z3_OP_UNINTERPRETED) {
                if (is_modal(current.decl)) { // Modal operator
                    SASSERT(current.decl.name().str() == "Box");
                    SASSERT(current.world->get_parent());
                    expr oldW = get_world(current.world->get_parent()->get_id());
                    expr newW = get_world(current.world->get_id());
                    m_processed_args.top().push_back(z3::forall(newW, implies(m_relation[0](oldW, newW), args[0])));
                }
                else { // we attach the world sort
                    sort_vector domain(m_ctx);
                    for (const z3::expr& arg : args)
                        domain.push_back(arg.get_sort());
                    domain.push_back(m_world_sort);
                    args.push_back(expr(m_ctx, get_world(current.world->get_id())));

                    func_decl new_func = m_ctx.function(current.decl.name(), domain, current.decl.range());
                    m_processed_args.top().push_back(new_func(args));
                    if (!m_uf_to_id.contains(app.decl)) {
                        m_uf_list.push_back(app.decl);
                        m_uf_to_id[app.decl] = m_uf_to_id.size();
                    }
                }
            }
            else
                m_processed_args.top().push_back(current.decl(args));
        }
    }

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

void modal_to_qeuf::output_model(const model& model, std::ostream& ostream) {
    expr_vector domain = expr_vector(m_ctx, Z3_model_get_sort_universe(m_ctx, model, m_world_sort));
    for (const auto& r : m_relation) {
        ostream << "Relation " << r.name().str() << ":\n";
        unsigned w1i = 1; 
        for (const auto& w1 : domain) {
            unsigned w2i = 0;
            w1i++;
            unsigned output_cnt = 0;
            for (const auto& w2 : domain) {
                w2i++;
                if (!model.eval(r(w1, w2), true).is_true())
                    continue;
                output_cnt++;
                ostream << "\tw" << w1i << " -> w" << w2i << "\n"; 
            }
            if (output_cnt > 0)
                ostream << "\n";
        }
    }
    
    ostream << "\n";
    
    for (const auto& uf : m_uf_list) {
        ostream << uf.name().str().c_str() << ":\n";
        if (uf.arity() != 1) {
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
