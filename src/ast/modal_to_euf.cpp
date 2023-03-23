#include <stack>

#include "modal_to_euf.h"
#include "assertion.h"

#if 0

z3::expr instantiate(modal_tree_node* n) {
    z3::expr_vector dst(n->world_constant().ctx());
    dst.push_back(n->world_constant());
    z3::expr e = n->get_syntax_node()->get_template().substitute(dst);
    return e;
}

z3::expr_vector modal_to_euf::apply_syntax_tree() const {
    struct to_process_struct {
        modal_tree_node* src;
        modal_tree_node* dst;
        to_process_struct(modal_tree_node* src, modal_tree_node* dst) : src(src), dst(dst) { }
    };
    
    std::stack<to_process_struct> to_process;
    to_process.push(to_process_struct(m_modal_tree->get_root(), m_modal_tree->get_root()));
    z3::expr_vector ret(m_ctx);
    
    // Diamond
    auto create = [&to_process](modal_tree_node* parent, modal_tree_node* new_world) {
        for (auto child : *parent) {
            if (child == parent) 
                continue;
            SASSERT(!new_world->has_propagated_by(child->get_syntax_node()));
            new_world->set_propagated_by(child->get_syntax_node(), true);
            to_process.push({ child, new_world });
        } 
    };
    
    // Box
    auto spread = [&to_process](modal_tree_node* parent, modal_tree_node* new_world) {
        for (auto child : *parent) {
            if (child == parent) 
                continue;
            SASSERT(!new_world->has_propagated_by(child->get_syntax_node()));
            new_world->set_propagated_by(child->get_syntax_node(), true);
            to_process.push({ child, new_world });
        } 
    };
    
    while (!to_process.empty()) {
        to_process_struct current = to_process.top();
        SASSERT(current.src);
        to_process.pop();
        ret.push_back(instantiate(current.src));
        for (const auto& child : *current.src->get_syntax_node()) {
            z3::expr world_constant = get_world_constant(m_modal_tree->size());
            z3::expr aux_predicate = info(child)->m_aux(world_constant);
            modal_tree_node* new_node = m_modal_tree->create_node(child, current.src, world_constant, aux_predicate);
            
            create(current.src, new_node);
            spread(new_node);
            to_process.push({ new_node, });
        }
    }
}

void modal_to_euf::prepare_expr(const expr_info &current, expr_vector &args) {
    
    if (current.decl.decl_kind() == Z3_OP_UNINTERPRETED) {
        if (is_modal(current.decl)) { // Modal operator
            SASSERT(current.decl.name().str() == "Box");
            SASSERT(current.world->get_parent());
            expr x(m_ctx, Z3_mk_bound(m_ctx, 0, m_world_sort));
            if (current.world->m_info) {
                m_processed_args.top().push_back(info(current.world)->m_aux(x));
            } 
            else {
                func_decl aux = m_ctx.function(("MAux" + std::to_string(current.world->get_id())).c_str(), m_world_sort, m_ctx.bool_sort());
                current.world->m_info = new euf_info(aux);
                m_processed_args.top().push_back(aux(x));
            }
        }
        else { // we attach the world sort
            sort_vector domain(m_ctx);
            for (const z3::expr& arg : args)
                domain.push_back(arg.get_sort());
            domain.push_back(m_world_sort);
            expr x(m_ctx, Z3_mk_bound(m_ctx, 0, m_world_sort));
            args.push_back(x);
        
            func_decl new_func = m_ctx.function(current.decl.name(), domain, current.decl.range());
            m_processed_args.top().push_back(new_func(args));
            
            if (!m_uf_set.contains(new_func.name().str())) {
                m_uf_set.insert(new_func.name().str());
                m_uf_list.push_back(new_func);
            }
        }
    }
    strategy::prepare_expr(current, args);
}

modal_to_euf::modal_to_euf(context& ctx) : 
        modal_to_euf_base(ctx) { }

void modal_to_euf::output_model(const model& model, std::ostream& ostream){
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
#endif
