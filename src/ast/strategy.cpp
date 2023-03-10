#pragma once

#include "assertion.h"
#include "logging.h"
#include "strategy.h"

bool strategy::is_modal(const func_decl& decl) const {
    return decl.arity() == 1 && decl.domain(0).is_bool() && (decl.name().str() == "Diamond" || decl.name().str() == "Box");
}

strategy::strategy(context& ctx, bool simplify) : m_ctx(ctx), m_last_result(z3::unknown), m_solver(), m_simplify(simplify) { }

expr strategy::simplify(const expr& e) {
    std::stack<expr_info> expr_to_process;
    expr_to_process.push({ e, Z3_L_TRUE, nullptr });
    SASSERT(m_processed_args.empty());
    SASSERT(m_apply_list.empty());
    m_processed_args.push({});
    modal_cnt = 0;
    
    // ASTs might be highly deeply nested. Rather use iteration than recursion
    while (!expr_to_process.empty()) {
        expr_info current = expr_to_process.top();
        expr_to_process.pop();
        
        VERIFY(current.e.is_app()); // For now
        LOG("Parsing (Simplify): " << current.e);
        if (!add_children_or_rewrite(expr_to_process, current, false))
            continue; // We rewrote the expression
            
        m_apply_list.push(current);
        m_processed_args.push({});
        
        
        while (!m_apply_list.empty() && (m_apply_list.top().arity <= m_processed_args.top().size()))) {

            expr_info app = m_apply_list.top();
            m_apply_list.pop();
            expr_vector args(m_ctx);
            
            LOG("Processing " << app.decl.name() << " / " << app.arity << (app.arity > 0 ? " with" : ""));
            for (unsigned i = 0; i < app.arity; i++) {
                args.push_back(m_processed_args.top()[i]);
                LOG("\t" << args.back());
            }
            m_processed_args.pop();
            
            if (!simplify(app, args))
                continue; // We simplified
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
    
    return m_processed_args.top()[0];
}

expr strategy::internalize(const expr& e) {
    std::stack<expr_info> expr_to_process;
    expr_to_process.push({ e, Z3_L_TRUE, 0, 0 });
    SASSERT(m_processed_args.empty());
    SASSERT(m_apply_list.empty());
    m_processed_args.push({});
    modal_cnt = 0;
    
    // ASTs might be highly deeply nested. Rather use iteration than recursion
    while (!expr_to_process.empty()) {
        expr_info current = expr_to_process.top();
        expr_to_process.pop();
        
        VERIFY(current.e.is_app()); // For now
        LOG("Parsing: " << current.e);
        if (!add_children_or_rewrite(expr_to_process, current, false))
            continue; // We rewrote the expression
            
        m_apply_list.push(current);
        m_processed_args.push({});
        
        
        while (!m_apply_list.empty() && (m_apply_list.top().arity <= m_processed_args.top().size() || (is_incremental_parsing() && is_modal(m_apply_list.top().decl)))) {

            expr_info app = m_apply_list.top();
            m_apply_list.pop();
            expr_vector args(m_ctx);
            
            LOG("Processing " << app.decl.name() << " / " << app.arity << (app.arity > 0 ? " with" : ""));
            for (unsigned i = 0; i < app.arity; i++) {
                args.push_back(m_processed_args.top()[i]);
                LOG("\t" << args.back());
            }
            m_processed_args.pop();
            
            if (!simplify(app, args))
                continue; // We simplified
            create_app(app, args);
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
    
    return m_processed_args.top()[0];
}

void strategy::collect_modals(const expr& e) {
    std::stack<expr_info> expr_to_process;
    expr_to_process.push({ e, Z3_L_TRUE, nullptr });
    world* w = create_world(expr_to_process.top());
    m_worlds.get_or_create(0, w);
    expr_to_process.top().world = w; 
            
    SASSERT(m_processed_args.empty());
    modal_cnt = 0;
    std::vector<expr_info> modals;
    
    // ASTs might be highly deeply nested. Rather use iteration than recursion
    while (!expr_to_process.empty()) {
        expr_info current = expr_to_process.top();
        expr_to_process.pop();
        
        VERIFY(current.e.is_app()); // For now
        LOG("Parsing: " << current.e);
        if (!add_children_or_rewrite(expr_to_process, current, true))
            continue; // We rewrote the expression
        if (is_modal(current.decl))
            add_modal(expr_to_process, current); // TODO: check if already present
    }
}

void strategy::incremental_internalize(const expr& e) {
    if (!is_incremental_parsing()) {
        internalize(e);
        return;
    }
    collect_modals(e);
}

static Z3_lbool invert_polarity(Z3_lbool current) {
    if (current == Z3_L_UNDEF)
        return Z3_L_UNDEF;
    if (current == Z3_L_FALSE)
        return Z3_L_TRUE;
    return Z3_L_FALSE;
}

bool strategy::add_children_or_rewrite(std::stack<expr_info>& expr_to_process, expr_info& current, bool analyze){
    const expr& e = current.e;
    
    auto add_to_process = [&expr_to_process, &current](Z3_lbool polarity) {
        for (unsigned i = current.e.num_args(); i > 0; i--) {
            expr_to_process.push(expr_info(current.e.arg(i - 1), polarity, current.contained_modal_id, current.modal_id));
        }
    };
    
    if (e.is_distinct()) {
        add_to_process(Z3_L_UNDEF);
        return true;
    }
    if (e.is_ite()) {
        add_to_process(Z3_L_UNDEF);
        return true;
    }
    
    // polarity separation not always possible: e.g., \lnot P(\Box Q) - We cannot say if \Box Q may be assumed to be true/false 
    if (e.is_eq()) {
        if (e.arg(0).get_sort().is_bool() && is_blast_eq()) {
            expr_to_process.push(expr_info(implies(current.e.arg(0), current.e.arg(1)) && implies(current.e.arg(1), current.e.arg(0)), current.polarity, current.contained_modal_id, current.modal_id));
            return false;
        }
        else {
            add_to_process(Z3_L_UNDEF);
            return true;
        }
    }
    if (e.is_implies()) {
        expr_to_process.push(expr_info(!current.e.arg(0) || current.e.arg(1), current.polarity, current.contained_modal_id, current.modal_id));
        return false;
    }
    
    if (is_modal(e.decl())) {
        current.modal_id = ++modal_cnt;
        if (!analyze)
            add_modal(expr_to_process, current);
        else
            expr_to_process.push(expr_info(current.e.arg(0), current.polarity, current.modal_id, current.modal_id));
        return true;
    }
    
    if (e.decl().decl_kind() == Z3_OP_UNINTERPRETED) {
        add_to_process(Z3_L_UNDEF); // we do not want to consider the case e.g., P(!a || b) [maybe even disable it?]
        return true;
    }
    
    if (e.is_not())
        add_to_process(invert_polarity(current.polarity));
    else
        add_to_process(current.polarity);
    return true;
}

// TODO: Convert to NNF? [use polarity information to remove all negations and apply de'morgan based on polarity]
bool strategy::simplify(expr_info& current, expr_vector& args) {
    if (!m_simplify)
        return true;
    if (current.decl.decl_kind() == Z3_OP_NOT) {
        if (args[0].is_not()) {
            m_processed_args.top().push_back(args[0].arg(0));
            return false;
        }
        else if (args[0].is_false()) {
            m_processed_args.top().push_back(current.e.ctx().bool_val(true));
            return false;
        }
        else if (args[0].is_true()) {
            m_processed_args.top().push_back(current.e.ctx().bool_val(false));
            return false;
        }
        return true;
    }
    if (current.decl.decl_kind() == Z3_OP_AND) {
        unsigned last = 0;
        const unsigned sz = args.size();
        for (unsigned i = 0; i < sz; i++) {
            if (args[i].is_false()) {
                m_processed_args.top().push_back(current.e.ctx().bool_val(false));
                return false;
            }
            else if (!args[i].is_true()) {
                if (last != i) {
                    expr e = args[i];
                    expr e2 = args[last];
                    args.set(i, e2);
                    args.set(last, e);
                }
                last++;
            }
        }
        if (last == 0) {
            m_processed_args.top().push_back(current.e.ctx().bool_val(true));
            return false;
        }
        else if (last == 1) {
            m_processed_args.top().push_back(args[0]);
            return false;
        }
        SASSERT(last <= args.size());
        current.arity = last;
        args.resize(last);
        return true;
    }
    if (current.decl.decl_kind() == Z3_OP_OR) {
        unsigned last = 0;
        const unsigned sz = args.size();
        for (unsigned i = 0; i < sz; i++) {
            if (args[i].is_true()) {
                m_processed_args.top().push_back(current.e.ctx().bool_val(true));
                return false;
            }
            else if (!args[i].is_false()) {
                if (last != i) {
                    expr e = args[i];
                    expr e2 = args[last];
                    args.set(i, e2);
                    args.set(last, e);
                }
                last++;
            }
        }
        if (last == 0) {
            m_processed_args.top().push_back(current.e.ctx().bool_val(false));
            return false;
        }
        else if (last == 1) {
            m_processed_args.top().push_back(args[0]);
            return false;
        }
        SASSERT(last <= args.size());
        current.arity = last;
        args.resize(last);
        return true;
    }
    if (is_modal(current.decl)) {
        if (current.decl.name().str() == "Box") {
            if (args[0].is_true()) {
                m_processed_args.top().push_back(current.e.ctx().bool_val(true));
                return false; 
            }
        }
        else {
            SASSERT(current.decl.name().str() == "Diamond");
            if (args[0].is_false()) {
                m_processed_args.top().push_back(current.e.ctx().bool_val(false));
                return false; 
            }
        }
        return true;
    }
    return true;
}

void strategy::add_modal(std::stack<expr_info>& expr_to_process, expr_info& current) {
    world& contained_world = m_worlds.get(current.contained_modal_id);
    world& current_world = m_worlds.get_or_create(current.modal_id, create_world(current));
    contained_world.create_relation(current.e.ctx(), current_world);
}

world* strategy::create_world(expr_info& info) {
    return new world(info);
}

check_result strategy::check(const expr& e) {
    if (!m_solver.has_value())
        m_solver = solver(m_ctx);
    
    LOG("Raw input:\n" << e << "\n");
    expr processed = incremental_internalize(e);
    LOG("\nProcessed:\n" << processed << "\n");
    m_solver->add(processed);
    m_last_result = m_solver->check();
    return m_last_result;
}

void strategy::output_state(std::ostream & ostream) {
    if (!m_solver) {
        ostream << "No result yet!\n";
        return;
    }
    switch (m_last_result) {
        case sat:
            ostream << "SAT:\n";
            output_model(m_solver->get_model(), ostream);
            break;
        case unsat:
            ostream << "UNSAT\n";
            break;
        default:
            ostream << "UNKNOWN:\n\t" << m_solver->reason_unknown();
            break;
    }
}

