#include "assertion.h"
#include "logging.h"
#include "strategy.h"
#include "parse_exception.h"

bool strategy::is_modal(const func_decl& decl) const {
    return eq(decl, m_decls.box) || eq(decl, m_decls.dia);
}

strategy::strategy(context& ctx, const modal_decls& decls) :
    m_ctx(ctx), m_solver(m_ctx), m_syntax_tree(nullptr), m_last_result(z3::unknown),
    m_decls(decls), m_uf_list(ctx), m_relation_list(ctx) {}


expr strategy::simplify_formula(const expr& e) {
    std::stack<expr_info> expr_to_process;
    expr_to_process.push(expr_info(e));
    SASSERT(m_processed_args.empty());
    SASSERT(m_apply_list.empty());
    m_processed_args.push({});
    
    // ASTs might be highly deeply nested. Rather use iteration than recursion
    while (!expr_to_process.empty()) {
        expr_info current = expr_to_process.top();
        expr_to_process.pop();
        
        VERIFY(current.e.is_app()); // For now
        LOG("Parsing (1): " << current.e);
        if (!pre_rewrite(expr_to_process, current))
            continue; // We rewrote the expression
            
        m_apply_list.push(current);
        m_processed_args.push({});
        
        while (!m_apply_list.empty() && (m_apply_list.top().arity <= m_processed_args.top().size())) {

            expr_info app = m_apply_list.top();
            m_apply_list.pop();
            expr_vector args(m_ctx);
            
            LOG("Processing (1) " << app.decl.name() << " / " << app.arity << (app.arity > 0 ? " with" : ""));
            for (unsigned i = 0; i < app.arity; i++) {
                args.push_back(m_processed_args.top()[i]);
                LOG("\t" << args.back());
            }
            m_processed_args.pop();
            
            post_rewrite(app, args);
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

bool strategy::pre_rewrite(std::stack<expr_info>& expr_to_process, expr_info& current){
    const expr& e = current.e;
    
    auto add_to_process = [&expr_to_process, &current]() {
        for (unsigned i = current.e.num_args(); i > 0; i--) {
            expr_to_process.push(expr_info(current.e.arg(i - 1)));
        }
    };
    
    // polarity separation not always possible: e.g., \lnot P(\Box Q) - We cannot say if \Box Q may be assumed to be true/false 
    if (e.is_eq()) {
        if (e.arg(0).get_sort().is_bool() && is_blast_eq()) {
            expr_to_process.push(expr_info(implies(current.e.arg(0), current.e.arg(1)) && implies(current.e.arg(1), current.e.arg(0))));
            return false;
        }
        else {
            add_to_process();
            return true;
        }
    }
    if (e.is_implies()) {
        expr_to_process.push(expr_info(!current.e.arg(0) || current.e.arg(1)));
        return false;
    }
    
    if (is_modal(e.decl())) {
        if (!current.e.arg(0).is_const())
            throw parse_exception("The relation in " + current.e.to_string() + " has to be a constant");
        // Transform to box-only form by duality (for simplicity)
        if (eq(e.decl(), m_decls.dia)) {
            expr_to_process.push(expr_info(!m_decls.box(current.e.arg(0), !current.e.arg(1))));
            return false;
        }
        add_to_process();
        return true;
    }
    
    add_to_process();
    return true;
}

// TODO: Convert to NNF?
bool strategy::post_rewrite(expr_info& current, expr_vector& args) {
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
        m_processed_args.top().push_back(current.decl(args));
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
        m_processed_args.top().push_back(current.decl(args));
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
        m_processed_args.top().push_back(current.decl(args));
        return true;
    }
    if (is_modal(current.decl)) {
        SASSERT(eq(current.decl, m_decls.box));
        if (args[1].is_true()) {
            m_processed_args.top().push_back(current.e.ctx().bool_val(true));
            return false;
        }
        m_processed_args.top().push_back(current.decl(args));
        return true;
    }
    if (eq(current.decl, m_decls.global)) {
        if (current.e.arg(0).is_false()) {
            m_processed_args.top().push_back(current.e.ctx().bool_val(true));
            return false;
        }
        if (current.e.arg(1).is_true()) {
            m_processed_args.top().push_back(current.e.ctx().bool_val(true));
            return false;
        }
        m_processed_args.top().push_back(current.decl(args));
        return true;
    }
    m_processed_args.top().push_back(current.decl(args));
    return true;
}

expr strategy::simplify(const expr& e) {
    return simplify_formula(e);
}

check_result strategy::check(expr e) {
    LOG("Raw input:\n" << e << "\n");
    e = simplify_formula(e); // we need to call this to collect uf/relation information [maybe separate later]
    LOG2("\nProcessed:\n" << e << "\n");
    e = create_formula(e);
    LOG("Adding: " << e);
    m_is_solving = true;
    if (!m_is_benchmark) {
        m_last_result = solve(e);
        m_is_solving = false;
        return m_last_result;
    }
    auto start = std::chrono::high_resolution_clock::now();
    m_last_result = solve(e);
    auto end = std::chrono::high_resolution_clock::now();
    m_solving_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
    m_is_solving = false;
    return m_last_result;
}

void strategy::output_state(std::ostream& ostream) {
    if (!m_solver) {
        ostream << "No result yet!\n";
        return;
    }
    switch (m_last_result) {
        case sat:
            ostream << "SAT:\n";
            output_model(m_solver.get_model(), ostream);
            break;
        case unsat:
            ostream << "UNSAT\n";
            break;
        default:
            ostream << "UNKNOWN:\n\t" << m_solver.reason_unknown();
            break;
    }
    std::flush(ostream);
}

