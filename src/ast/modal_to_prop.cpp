#pragma once

#include <stack>

#include "modal_to_prop.h"
#include "assertion.h"

void modal_to_prop::create_app(const expr_info& current, expr_vector &args) {
    
    world& current_world = get_world(current.contained_modal_id);
    
    if (current.decl.decl_kind() == Z3_OP_UNINTERPRETED) {
        if (is_modal(current.decl)) { // Modal operator
            VERIFY(current.modal_id != current.contained_modal_id);
            worlds_to_process.push_back(current);
        }
        else { // we attach the world sort
            VERIFY(current.modal_id == current.contained_modal_id);
            sort_vector domain(m_ctx);
            for (unsigned i = 0; i < args.size(); i++)
                domain.push_back(args[i].get_sort());
            
            m_processed_args.top().push_back(current_world.add_atom(current.decl, args));
            
            if (!m_uf_set.contains(current.decl.name().str())) {
                m_uf_set.insert(current.decl.name().str());
                m_uf_list.push_back(current.decl);
            }
        }
    }
    else {
        // We just reuse the same decl
        VERIFY(current.modal_id == current.contained_modal_id);
        m_processed_args.top().push_back(current.decl(args));
    }
}

modal_to_prop::modal_to_prop(context& ctx, bool simplify) : 
        strategy(ctx, simplify),
        m_worlds(),
        m_uf_list(ctx) { }

void modal_to_prop::output_model(const model& model, std::ostream& ostream){
    /*expr_vector domain = expr_vector(m_ctx, Z3_model_get_sort_universe(m_ctx, model, m_world_sort));
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
    }*/
    
}
