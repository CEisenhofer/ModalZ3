#include <algorithm>
#include <cstring>
#include "lazy_up.h"
#include "parse_exception.h"

std::ostream& operator<<(std::ostream& os, undo_trail* undo) {
    undo->output(os);
    return os;
}

void assignment_undo::undo() {
    m_world->unassign(m_var);
}

void create_world_undo::undo() {
    m_modal_tree->remove_last_child(m_relation);
}

void add_spread_info_undo::undo() {
    m_world->remove_last_spread(m_relation);
}

void added_init_info_undo::undo() {
    SASSERT(!m_to_init.empty());
    SASSERT(m_to_init.back().m_template == m_to_remove.m_template && 
        m_to_init.back().m_parent == m_to_remove.m_parent); // TODO: Non-chronological. This might fail if elements are blocked
    m_to_init.pop_back();
}

void removed_init_info_undo::undo() {
    m_to_init.push_back(m_info);
}

void log_clause(expr const& proof, expr_vector const& clause) {
    //LOG("Proof: " << proof);
    //LOG("Clause: " << clause);
}

void lazy_up::propagate_to(modal_tree_node* new_world, unsigned relation) {
    SASSERT(!new_world->is_root());
    modal_tree_node* parent = new_world->get_parent();
    if (relation >= parent->get_spread_relation_cnt())
        return;
    for (const auto& box : parent->get_spread(relation)) {
        expr e = box.m_template->initialize(new_world->world_constant(), true);
        LOG("Propagating (SP): " << !new_world->aux_predicate() << " && " << box.m_justification << " => " << e);
        propagate(new_world->aux_predicate(), box.m_justification,  e);
    }
}

void lazy_up::propagate_from(syntax_tree_node* temp, modal_tree_node* parent, unsigned relation, const expr& justification) {
    if (relation >= parent->get_child_relations_cnt())
        return;
    for (const auto& child : parent->get_children(relation)) {
        expr e = temp->initialize(child->world_constant(), true);
        LOG("Propagating (SP): " << !child->aux_predicate() << " && " << justification  << " => " << e);
        propagate(child->aux_predicate(), justification, e);
    }
}

void lazy_up::apply_unconstrained(modal_tree_node* world) {
    z3::expr_vector args(ctx());
    args.push_back(world->world_constant());
    for (syntax_tree_node* n : m_unconstraint_global) {
        LOG("Unconditional constraint: " + n->get_template(true).to_string() + " to world " + world->world_constant().to_string());
        propagate(world->aux_predicate(), n->get_template(true).substitute(args));
    }
}


unsigned lazy_up::get_variable(const func_decl& decl) const {
    auto it = m_uf_to_id.find(decl);
    if (it == m_uf_to_id.end())
        return -1;
    return it->second;
}

unsigned lazy_up::get_or_create_variable(const func_decl& decl) {
    unsigned id = get_variable(decl);
    if (id != -1)
        return id;
    id = m_uf_to_id.size();
    m_uf_to_id[decl] = id;
    return id;
}

void lazy_up::add_constraint(const func_decl & var, bool neg, syntax_tree_node* rhs) {
    unsigned id = get_or_create_variable(var);
    for (unsigned i = m_unconstraint_global.size(); i < 2 * (id + 1); i++) {
        m_constraint_global.emplace_back();
    }
    m_constraint_global[2 * id + neg].push_back(rhs);
}

expr lazy_up::create_formula(const expr& e) {
    std::stack<expr_info> expr_to_process;
    std::stack<expr_info> subformulas_to_process;
    expr_info info(e);
    info.top_level = true;

    m_syntax_tree = new syntax_tree(this);
    info.world = m_syntax_tree->get_root();

    subformulas_to_process.push(info);

    while (!subformulas_to_process.empty()) {
        info = subformulas_to_process.top();
        expr_to_process.push(info);
        subformulas_to_process.pop();

        SASSERT(m_processed_args.empty());
        SASSERT(m_apply_list.empty());
        m_processed_args.push({});


        while (!expr_to_process.empty()) {
            expr_info current = expr_to_process.top();
            expr_to_process.pop();

            VERIFY(current.e.is_app());
            LOG("Parsing (2): " << current.e);

            if (is_modal(current.decl)) {
                SASSERT(is_box(current.decl));
                syntax_tree_node* existing;
                if ((existing = current.world->get_child_by_expr(current.e)) == nullptr) {

                    unsigned relation_id;
                    expr relation = current.e.arg(0);
                    if (!relation.is_const())
                        throw parse_exception("Relations have to be constants unlike " + relation.to_string());
                    if (!m_relation_to_id.contains(relation.decl())) {
                        relation_id = m_relation_to_id.size();
                        m_relation_to_id[relation.decl()] = relation_id;
                        m_relation_list.push_back(relation.decl());
                    }
                    else {
                        relation_id = m_relation_to_id[relation.decl()];
                    }

                    syntax_tree_node* new_node = m_syntax_tree->create_node(current.world, relation_id, current.e);
                    SASSERT(get_variable(new_node->get_aux().decl()) == -1);
                    m_uf_to_id[new_node->get_aux().decl()] = m_uf_to_id.size();
                    LOG("Adding: " << new_node->get_aux().decl().name().str());

                    current.world = new_node;
                    LOG("New potential world: " << new_node->get_id() << " with parent " << (new_node->is_root() ? " root " : std::to_string(new_node->get_parent()->get_id())));
                    current.e = current.e.arg(1);
                    current.decl = current.e.decl();
                    current.arity = current.e.num_args();
                    LOG("Pushing: " << current.e.to_string());
                    subformulas_to_process.push(current);
                }
                else
                    current.world = existing;

                m_processed_args.top().push_back(current.world->get_aux());
            }
            else if (is_global(current.decl)) {
                if (!current.top_level)
                    throw parse_exception("\"global\" may only occur top-level");
                syntax_tree_node* new_node = m_syntax_tree->create_node(current.e);
                current.world = new_node;
                LOG("New global constraint: " << new_node->get_id());
                expr lhs = current.e.arg(0);
                expr rhs = current.e.arg(1);
                current.e = rhs;
                current.decl = rhs.decl();
                current.arity = rhs.num_args();
                LOG("Pushing: " << lhs.to_string() << " |= " << rhs.to_string());
                subformulas_to_process.push(current);
                if (lhs.is_true()) {
                    add_unconstraint(new_node);
                }
                else {
                    bool neg = lhs.is_not();
                    if (neg)
                        lhs = lhs.arg(0);
                    if (lhs.decl().decl_kind() != Z3_OP_UNINTERPRETED || lhs.num_args() != 1 || !z3::eq(lhs.arg(0).get_sort(), m_decls.world_sort) || !z3::eq(lhs.arg(0).get_sort(), m_decls.placeholder))
                        throw parse_exception("For now, the lhs of \"global\" must be a generalized propositional variable");
                    add_constraint(lhs.decl(), neg, new_node);
                }
                m_processed_args.top().push_back(ctx().bool_val(true));
            }
            else {
                for (unsigned i = current.e.num_args(); i > 0; i--) {
                    expr_info info2(current.e.arg(i - 1));
                    info2.world = current.world;
                    info2.top_level = current.top_level && current.decl.decl_kind() == Z3_OP_AND;
                    expr_to_process.push(info2);
                }

                m_apply_list.push(current);
                m_processed_args.push({});
            }

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

                if (app.decl.decl_kind() == Z3_OP_UNINTERPRETED && !z3::eq(app.decl.range(), m_decls.world_sort) && !z3::eq(app.decl.range(), m_decls.relation_sort)) {
                    // for now: always flexible interpretation
                    sort_vector domain(m_ctx);
                    for (const z3::expr& arg : args)
                        domain.push_back(arg.get_sort());
                    if (!args.empty() && z3::eq(args[0].get_sort(), m_decls.world_sort)) {
                        if (!is_placeholder(args[0].decl())) {
                            throw parse_exception("Currently not supporting ABox/complex world terms: " + current.e.to_string());
                        }
                        auto ast = (z3::ast)z3::expr(ctx(), Z3_mk_bound(ctx(), 0, m_decls.world_sort));
                        args.set(0, ast); // replace by placeholder
                    }
                    bool is_up = app.decl.range().is_bool() || app.decl.range().is_bv();
                    func_decl new_func = is_up
                            ? m_ctx.user_propagate_function(app.decl.name(), domain, app.decl.range())
                            : m_ctx.function(app.decl.name(), domain, app.decl.range());
                    
                    m_processed_args.top().push_back(new_func(args));
                    if (!m_uf_set.contains(new_func)) {
                        LOG("Adding: " << new_func.name().str());
                        m_orig_uf_to_new_uf[app.decl] = new_func;
                        m_uf_list.push_back(new_func);
                        m_uf_set.insert(new_func);
                        if (is_up)
                            m_uf_to_id[new_func] = m_uf_to_id.size();
                    }
                }
                else
                    m_processed_args.top().push_back(app.decl(args));
            }
        }

        expr t = m_processed_args.top().back();
        info.world->set_template(t);
        LOG("Generated: " << info.world->to_string() << " with aux: " << info.world->aux_to_string());

        VERIFY(m_processed_args.size() == 1);
        if (m_processed_args.top().size() != 1) {
            for (unsigned i = 0; i < m_processed_args.top().size(); i++)
                LOG("\tInvalid element: " << m_processed_args.top()[i]);
        }
        VERIFY(m_processed_args.top().size() == 1);
        VERIFY(m_apply_list.empty());
        m_processed_args.pop();
    }

    delete m_modal_tree;
    m_modal_tree = new modal_tree(m_syntax_tree);
    z3::expr assertion = m_modal_tree->get_root()->get_syntax_node()->initialize(m_modal_tree->get_root()->world_constant(), true);
    
    expr_vector& new_operands = m_assertions;
    
    for (modal_tree_node* existing : m_modal_tree->get_existing_worlds())
        apply_unconstrained(existing);
    
    if (assertion.is_and()) {
        expr_vector operands(ctx());
        for (unsigned i = 0; i < assertion.num_args(); i++)
            operands.push_back(assertion.arg(i));
        
        while (!operands.empty()) {
            assertion = operands.back();
            operands.pop_back();
            if (assertion.is_and()) {
                for (unsigned i = 0; i < assertion.num_args(); i++)
                    operands.push_back(assertion.arg(i));
            }
            else if (!assertion.is_true()) {
                new_operands.push_back(assertion);
            }
        }
    }
    else if (!assertion.is_true())
        new_operands.push_back(assertion);
    
    if (new_operands.empty())
        return ctx().bool_val(true);
    if (new_operands.size() == 1)
        return new_operands[0];
    return z3::mk_and(new_operands);
}

void lazy_up::push() {
    m_trail_sz.push_back(m_trail.size());
}

void lazy_up::pop(unsigned num_scopes) {
    LOG("Undoing current state:\n" << *m_modal_tree << "\n");
    SASSERT(m_trail_sz.size() >= num_scopes);
    unsigned old_sz = m_trail_sz[m_trail_sz.size() - num_scopes];
    m_trail_sz.resize(m_trail_sz.size() - num_scopes);
    while (m_trail.size() > old_sz) {
        undo_trail* trail = m_trail.top();
        LOG("Undo: " << trail);
        m_trail.pop();
        trail->undo();
        delete trail;
    }
}

void lazy_up::fixed(const expr& e, const expr& value) {
    SASSERT(value.is_bool());
    bool v = value.is_true();
    LOG(e << " = " << value);
    func_decl func = e.decl();
    SASSERT(func.arity() > 0);
    expr arg = e.arg(0);
    SASSERT(z3::eq(arg.get_sort(), m_decls.world_sort));
    modal_tree_node* world = m_modal_tree->get(arg);
    unsigned var = get_variable(e.decl());
    SASSERT(var != -1);
    //SASSERT(!world->is_assigned(var));
    world->assign(var, v);
    add_trail(new assignment_undo(world, var));

    syntax_tree_node* abs = m_syntax_tree->get_node(func);
    if (abs) { // Modal operator; otw. just ordinary predicate
        m_to_init.push_back(init_info(abs, world, e, v));
        add_trail(new added_init_info_undo(m_to_init, m_to_init.back()));
    }

    //if (m_trail_sz.empty()) // Root level; we won't have to revert them
        // For some reason Z3 tends otw. to set consequences as irrelevant...
    //    final();
}

static int final_checks = 0;

void lazy_up::final() {
    try {
        if (m_trail_sz.empty())
            LOG("Eager check: " << ++final_checks);
        else
            LOG("Final check: " << ++final_checks);
        LOG("Current state: " << *m_modal_tree << "\n");
        // TODO: First negative; then positive [performance reasons] (we then now already where to spread to)
        // TODO: Delay box evaluation
        unsigned last = m_to_init.size();
        for (unsigned i = m_to_init.size(); i > 0; i--) {
            const auto& to_init = m_to_init[i - 1];
            if (to_init.m_parent->is_blocked()) { // TODO: Cache!
                m_to_init[--last] = m_to_init[i - 1];
                //LOG("World w" + std::to_string(to_init.m_parent->get_id()) + " blocked by w" + std::to_string(to_init.m_parent->blocked_by()->get_id()));
                continue;
            }
            add_trail(new removed_init_info_undo(m_to_init, to_init));
            const unsigned relation = to_init.m_template->get_relation();
            if (!to_init.m_positive) {
                modal_tree_node* new_world = m_modal_tree->get_or_create_node(to_init.m_template, to_init.m_parent, to_init.just());
                add_trail(new create_world_undo(m_modal_tree, relation));
                if (to_init.m_template->is_template_false()) {
                    LOG("Propagating (SK): No propagation required; body trivial");
                }
                else {
                    z3::expr inst = to_init.m_template->initialize(new_world->world_constant(), false);
                    propagate(to_init.just(), inst);
                    LOG("Propagating (SK): " << !to_init.just() << " => " << inst);
                }
                propagate_to(new_world, relation);
                apply_unconstrained(new_world);
            }
            else {
                spread_info info(to_init.m_template, to_init.just());
                to_init.m_parent->add_spread(info, to_init.m_template->get_relation());
                add_trail(new add_spread_info_undo(to_init.m_parent, relation));
                propagate_from(to_init.m_template, to_init.m_parent, relation, to_init.just());
            }
        }
        m_to_init.resize(m_to_init.size() - last);
    }
    catch (const exception& e) {
        if (strcmp(e.msg(), "canceled") != 0) {
            throw;
        }
    }
}

void lazy_up::created(const expr& e) {
    LOG("Encountered: " << e);
}

void lazy_up::decide(expr& e, unsigned& bit, Z3_lbool& val) {
    // TODO: Apply an initial "final"-call before the first push
    // TODO: Prefer having either all modalities positive/negative (slight preference for positive)
    // as number of propagations = (|Boxes| + 1) * |Diamonds|
    LOG("Splitting " << e << " = " << (val == Z3_L_TRUE ? "true" : "false"));
}

void lazy_up::output_model(const model& model, std::ostream& ostream) {

    unsigned ri = 0;
    for (const auto& r : m_relation_list) {
        ostream << "Relation " << r.name().str() << ":\n";
        for (modal_tree_node* n : m_modal_tree->get_existing_worlds()) {
            if (n->get_child_relations_cnt() <= ri)
                continue;
            for (modal_tree_node* child : n->get_children(ri)) {
                if (child->blocked_by()) {
                    ostream << "\tw" << n->get_id() << " -> w" << child->blocked_by()->get_id() << " [blocked]" << std::endl;
                }
                else {
                    ostream << "\tw" << n->get_id() << " -> w" << child->get_id() << std::endl;
                }
            }
        }
        ri++;
    }

    ostream << "\n";

    for (unsigned i = 0; i < m_uf_list.size(); i++) {
        const auto& uf = m_uf_list[i];
        ostream << uf.name().str().c_str() << ":\n";
        if (uf.arity() != 1)
            ostream << "\tSkipped because of complexity\n";
        else {
            for (modal_tree_node* n : m_modal_tree->get_existing_worlds()) {
                if (m_uf_to_id.contains(uf)) { // to also have "don't-cares" for booleans at least
                    unsigned id = m_uf_to_id[uf];
                    Z3_lbool val = n->get_assignment(id);
                    if (val != Z3_L_UNDEF)
                        ostream << "\tw" << n->get_id() << ": " << (val == Z3_L_TRUE ? "true" : "false") << "\n";
                }
                else {
                    expr eval = model.eval(uf(n->world_constant()), true);
                    ostream << "\tw" << n->get_id() << ": " << eval << "\n";
                }
            }
            ostream << "\n";
        }
    }
}

struct check_info {
    
    modal_tree_node* world;
    z3::expr original_expr;
    unsigned processed_idx = 0; // either the argument for normal operations or the child in case of modal operators
    std::vector<expr> args;
    
    check_info(modal_tree_node* w, const z3::expr& e) : world(w), original_expr(e) {}
    
    func_decl decl() const {
        return original_expr.decl();
    }
};

Z3_lbool lazy_up::model_check(const expr& e) {
    
    std::stack<check_info> to_process;
    to_process.push(check_info(m_modal_tree->get_root(), e));
    to_process.push(to_process.top());
    SASSERT(m_apply_list.empty());
    model m = m_solver.get_model();
    
    while (to_process.size() > 1) {
        const check_info current = to_process.top();
        
        func_decl f = current.decl();
        Z3_decl_kind kind = f.decl_kind();
        bool modal = is_modal(f);
        
        LOG("Checking " << current.original_expr << " with arg " << current.processed_idx);
        
        if (!modal && kind == Z3_OP_UNINTERPRETED) {
            // Prop. variables
            to_process.pop();
            if (current.original_expr.num_args() > 0 && z3::eq(f.domain(0), m_decls.world_sort)) {
                SASSERT(m_orig_uf_to_new_uf.contains(f));
                unsigned vid = get_variable(*(m_orig_uf_to_new_uf[f]));
                SASSERT(vid != -1);
                if (!current.world->is_assigned(vid)) {
                    //to_process.top().args.push_back(current.original_expr);
                    to_process.top().args.push_back(m_ctx.bool_val(false)); // completion to please MC
                }
                else {
                    to_process.top().args.push_back(ctx().bool_val(current.world->get_assignment(vid) == Z3_L_TRUE));
                }
            }
            else {
                to_process.top().args.push_back(m.eval(current.original_expr, true)); // completion to please MC
            }
            continue;
        }
        
        unsigned max;
        unsigned relation_id;
        if (modal) {
            relation_id = m_relation_to_id.contains(current.original_expr.arg(0).decl()) 
                    ? m_relation_to_id[current.original_expr.arg(0).decl()]
                    : -1; // the relation might be optimized away. Hence, there are no such children
            max = current.world->get_child_relations_cnt() > relation_id ? current.world->get_children(relation_id).size() : 0;
        }
        else if (is_global(f)) {
            max = m_modal_tree->existing_size();
        }
        else{
            max = current.original_expr.num_args();
        }
        
        if (!current.args.empty()) {
            if (kind == Z3_OP_AND || (modal && is_box(f))) {
                if (to_process.top().args.back().is_false()) {
                    to_process.pop();
                    to_process.top().args.push_back(ctx().bool_val(false));
                    continue;
                }
            }
            else if (kind == Z3_OP_OR || (modal && is_dia(f))) {
                if (to_process.top().args.back().is_true()) {
                    to_process.pop();
                    to_process.top().args.push_back(ctx().bool_val(true));
                    continue;
                }
            }
            else if (kind == Z3_OP_IMPLIES) {
                SASSERT(to_process.top().args.size() <= 2);
                if (
                        (to_process.top().args.size() == 1 && to_process.top().args.back().is_false()) || 
                        (to_process.top().args.size() == 2 && to_process.top().args.back().is_true())) {
                    to_process.pop();
                    to_process.top().args.push_back(ctx().bool_val(true));
                    continue;
                }
            }
        }
        
        if (current.processed_idx >= max) {
            LOG("Final check for " << current.original_expr);
            std::vector<expr> args = std::move(to_process.top().args);
            to_process.pop();
            
            if (kind == Z3_OP_AND || is_box(f) || is_global(f)) {
                for (const auto& arg : args) {
                    SASSERT(!arg.is_false()); // otw. we would have detected earlier
                    if (!arg.is_true())
                        goto failed;
                }
                to_process.top().args.push_back(ctx().bool_val(true));
            }
            else if (kind == Z3_OP_OR || is_dia(f)) {
                for (const auto& arg : args) {
                    SASSERT(!arg.is_true()); // otw. we would have detected earlier
                    if (!arg.is_false())
                        goto failed;
                }
                to_process.top().args.push_back(ctx().bool_val(false));
            }
            else if (kind == Z3_OP_NOT) {
                SASSERT(args.size() == 1);
                if (args[0].is_true())
                    to_process.top().args.push_back(ctx().bool_val(false));
                else if (args[0].is_false())
                    to_process.top().args.push_back(ctx().bool_val(true));
                else
                    goto failed;
            }
            else if (kind == Z3_OP_IMPLIES) {
                SASSERT(args.size() == 2);
                SASSERT(!args[0].is_false()); // otw. we would have detected earlier
                SASSERT(!args[1].is_true());
                if (args[0].is_true() && args[1].is_false())
                    to_process.top().args.push_back(ctx().bool_val(false));
                else
                    goto failed;
            }
            else if (kind == Z3_OP_EQ) {
                SASSERT(args.size() == 2);
                if (
                        (args[0].is_true() && args[1].is_true()) ||
                        (args[0].is_false() && args[1].is_false()))
                    to_process.top().args.push_back(ctx().bool_val(true));
                else if (
                        (args[0].is_false() && args[1].is_true()) ||
                        (args[0].is_true() && args[1].is_false()))
                    to_process.top().args.push_back(ctx().bool_val(false));
                else
                    goto failed;
            }
            else {
                failed:
                to_process.top().args.push_back(current.original_expr); // cannot evaluate; just keep it
            }
            continue;
        }
        
        if (modal) {
            to_process.push({ current.world->get_children(relation_id)[to_process.top().processed_idx++], current.original_expr.arg(1) });
        }
        else if (is_global(f)) {
            to_process.push({ m_modal_tree->get_existing_worlds()[to_process.top().processed_idx++], current.original_expr.arg(0) });
        }
        else {
            to_process.push({ current.world, current.original_expr.arg(to_process.top().processed_idx++) });
        }
    }
    
    SASSERT(to_process.size() == 1);
    SASSERT(to_process.top().args.size() == 1);
    expr ret = to_process.top().args[0];
    if (!ret.is_true() && !ret.is_false()) {
        std::cout << "Incomplete model: " << ret << std::endl; 
    }
    return ret.is_true() ? Z3_L_TRUE : ret.is_false() ? Z3_L_FALSE : Z3_L_UNDEF;
}

unsigned lazy_up::domain_size() {
    return m_modal_tree->existing_size();
}
