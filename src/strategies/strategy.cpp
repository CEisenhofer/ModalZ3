#include "assertion.h"
#include "logging.h"
#include "strategy.h"
#include "parse_exception.h"

z3::sort_vector modal_decls::get_sorts() {
    z3::sort_vector sorts(world_sort.ctx());
    sorts.push_back(world_sort);
    sorts.push_back(relation_sort);
    return sorts;
}

z3::func_decl_vector modal_decls::get_decls() {
    z3::func_decl_vector functions(world_sort.ctx());
    functions.push_back(box);
    functions.push_back(dia);
    functions.push_back(global);
    functions.push_back(reachable);
    functions.push_back(placeholder);
    return functions;
}

modal_decls modal_decls::create_default(context & ctx) {
    modal_decls decls(ctx.uninterpreted_sort("World"), ctx.uninterpreted_sort("Relation"));
    z3::sort_vector domain(ctx);
    func_decl placeholder = ctx.function("world", domain, decls.world_sort);
    decls.placeholder = placeholder;
    domain.push_back(decls.relation_sort);
    domain.push_back(ctx.bool_sort());
    decls.dia = ctx.function("dia", domain, ctx.bool_sort());
    decls.box = ctx.function("box", domain, ctx.bool_sort());

    decls.global = ctx.function("global", ctx.bool_sort(), ctx.bool_sort());
    decls.reachable = ctx.function("reachable", decls.relation_sort, decls.world_sort, decls.world_sort, ctx.bool_sort());
    return decls;
}

bool strategy::is_world(const sort& s) const {
    return z3::eq(s, m_decls.world_sort);
}

bool strategy::is_relation(const sort& s) const {
    return z3::eq(s, m_decls.relation_sort);
}

bool strategy::is_modal(const func_decl& decl) const {
    return is_box(decl) || is_dia(decl);
}

bool strategy::is_box(const func_decl& decl) const {
    return eq(decl, m_decls.box);
}

bool strategy::is_dia(const func_decl& decl) const {
    return eq(decl, m_decls.dia);
}

bool strategy::is_placeholder(const func_decl& decl) const {
    return eq(decl, m_decls.placeholder);
}

bool strategy::is_global(const func_decl &decl) const {
    return eq(decl, m_decls.global);
}

bool strategy::is_reachable_extern(const func_decl &decl) const {
    return eq(decl, m_decls.reachable);
}

bool strategy::is_ml_interpreted(const func_decl& decl) const {
    return is_modal(decl) || is_global(decl);
}

strategy::strategy(context& ctx, const modal_decls& decls) :
    m_ctx(ctx), m_solver(m_ctx), m_syntax_tree(nullptr), m_last_result(z3::unknown),
    m_decls(decls), m_uf_list(ctx), m_relation_list(ctx), m_solving_time() {
}


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
            z3::expr res = post_rewrite(app.decl, args);
            m_processed_args.top().push_back(res);
            LOG("Simpl. Subexpression: " << res);
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
        if (is_dia(e.decl())) {
            expr_to_process.push(expr_info(!m_decls.box(current.e.arg(0), !current.e.arg(1))));
            return false;
        }
        add_to_process();
        return true;
    }
    
    add_to_process();
    return true;
}

#define REMOVE_ARG(I)                           \
        do {                                    \
            z3::expr t = args[args.size() - 1]; \
            args.set(i, t);                     \
            args.pop_back();                    \
        } while (false)

// TODO: Convert to NNF?
z3::expr strategy::post_rewrite(const func_decl& f, expr_vector& args) {
    if (f.decl_kind() == Z3_OP_NOT) {
        if (args[0].is_not()) {
            return args[0].arg(0);
        }
        else if (args[0].is_false()) {
            return ctx().bool_val(true);
        }
        else if (args[0].is_true()) {
            return ctx().bool_val(false);
        }
        return f(args);
    }
    if (f.decl_kind() == Z3_OP_AND || f.decl_kind() == Z3_OP_OR) {
        const bool is_and = f.decl_kind() == Z3_OP_AND;
        std::unordered_map<z3::expr, bool, expr_hash, expr_eq> enc;
        std::unordered_map<z3::expr, std::optional<expr_vector>, expr_hash, expr_eq> modals;
        z3::expr_vector relations(ctx());
        unsigned i = 0;

        while (i < args.size()) {
            expr arg = args[i];
            LOG("Simplify " << (is_and ? "and" : "or") << " argument: " << arg);
            if ((is_and && arg.is_and()) || (!is_and && arg.is_or())) {
                // Flatten
                const unsigned sz = arg.num_args();
                SASSERT(sz > 1);
                expr a = arg.arg(0);
                args.set(i, a);
                for (unsigned j = 1; j < sz; j++)
                    args.push_back(arg.arg(j));
                continue;
            }
            else if ((is_and && arg.is_false()) || (!is_and && arg.is_true())) {
                return ctx().bool_val(!is_and);
            }
            else if ((is_and && arg.is_true()) || (!is_and && arg.is_false())) {
                REMOVE_ARG(i);
                continue;
            }
            else {
                bool neg = false;
                expr test = arg;
                if (arg.is_not()) {
                    test = arg.arg(0);
                    neg = true;
                }
                auto it = enc.find(test);
                if (it == enc.end()) {
                    enc[test] = neg;
                    if ((neg != is_and) && is_widen_modals() && is_box(test.decl())) {
                        z3::expr r = test.arg(0);
                        if (!modals[r].has_value()) {
                            modals[r] = z3::expr_vector(ctx());
                            relations.push_back(r);
                        }
                        modals[r]->push_back(test.arg(1));
                        REMOVE_ARG(i);
                        continue;
                    }
                }
                else if (it->second != neg) {
                    return ctx().bool_val(!is_and);
                }
                else {
                    REMOVE_ARG(i);
                    continue;
                }
            }
            i++;
        }
        // Merge modals again
        for (const auto& r : relations) {
            const auto& e = modals[r];
            SASSERT(e.has_value());
            z3::expr_vector a = e.value();
            // rewrite: this won't cascade as we evaluate bottom up:
            if (is_and) {
                args.push_back(m_decls.box(r, post_rewrite(f, a)));
            }
            else {
                expr processed = z3::mk_and(a);
                processed = post_rewrite(processed.decl(), a);
                args.push_back(!m_decls.box(r, processed));
            }
        }
        if (args.empty()) {
            return ctx().bool_val(is_and);
        }
        else if (args.size() == 1) {
            return args[0];
        }
        return f(args);
    }
    if (is_modal(f)) {
        SASSERT(is_box(f));
        if (args[1].is_true()) {
            return ctx().bool_val(true);
        }
        return f(args);
    }
    if (is_global(f)) {
        if (args[0].is_true()) {
            return ctx().bool_val(true);
        }
        return f(args);
    }
    return f(args);
}

#undef REMOVE_ARG

expr strategy::simplify(const expr& e) {
    return simplify_formula(e);
}

check_result strategy::check(expr e) {
    LOG("Raw input:\n" << e << "\n");
    e = simplify_formula(e); // we need to call this to collect uf/relation information [maybe separate later]
    LOG2("\nProcessed:\n" << e << "\n");
    e = create_formula(e);
    LOG("SMT formula: " << e << "\n");
    m_is_solving = true;
    if (!m_is_benchmark) {
        try {
            m_last_result = solve(e);
        }
        catch (const exception& e) {
            m_last_result = z3::unknown; // sometimes because of timeout
        }
        m_is_solving = false;
        return m_last_result;
    }
    auto start = std::chrono::high_resolution_clock::now();
    try {
        m_last_result = solve(e);
    }
    catch (const exception& e) {
        m_last_result = z3::unknown; // sometimes because of timeout
    }
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
            ostream << "UNKNOWN:\n\t" << m_solver.reason_unknown() << "\n";
            break;
    }
    ostream << "\n";
    std::flush(ostream);
}
