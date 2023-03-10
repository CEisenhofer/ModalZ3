#pragma once

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

void modal_to_qeuf::create_app(const expr_info& current, expr_vector &args) {
    if (current.decl.decl_kind() == Z3_OP_UNINTERPRETED) {
        if (is_modal(current.decl)) { // Modal operator
            VERIFY(current.modal_id != current.contained_modal_id);
            expr oldW = get_world(current.contained_modal_id);
            expr newW = get_world(current.modal_id);
            SASSERT(args.size() == 1);
            if (current.decl.name().str() == "Diamond")
                m_processed_args.top().push_back(z3::exists(newW, m_relation[0](oldW, newW) && args[0])); // TODO: Check relation
            else
                m_processed_args.top().push_back(z3::forall(newW, implies(m_relation[0](oldW, newW), args[0])));
        }
        else { // we attach the world sort
            VERIFY(current.modal_id == current.contained_modal_id);
            sort_vector domain(m_ctx);
            for (unsigned i = 0; i < args.size(); i++)
                domain.push_back(args[i].get_sort());
            domain.push_back(m_world_sort);
            args.push_back(expr(m_ctx, get_world(current.modal_id)));
        
            func_decl new_func = m_ctx.function(current.decl.name(), domain, current.decl.range());
            m_processed_args.top().push_back(new_func(args));
            
            if (!m_uf_set.contains(new_func.name().str())) {
                m_uf_set.insert(new_func.name().str());
                m_uf_list.push_back(new_func);
            }
        }
    }
    else {
        VERIFY(current.modal_id == current.contained_modal_id);
        // We just reuse the same decl
        m_processed_args.top().push_back(current.decl(args));
    }
}

modal_to_qeuf::modal_to_qeuf(context& ctx, bool simplify) : 
        strategy(ctx, simplify), 
        m_world_sort(ctx.uninterpreted_sort(world_sort_name)),
        m_world_variables(ctx),
        m_relation(ctx),
        m_uf_list(ctx) {
    
        m_world_variables.push_back({ ctx, Z3_mk_fresh_const(ctx, "World", m_world_sort) });
        m_relation.push_back(ctx.function("R", m_world_sort, m_world_sort, ctx.bool_sort())); // TODO: Muli-Modal
}

void modal_to_qeuf::output_model(const model& model, std::ostream& ostream){
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
