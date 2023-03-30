#include <algorithm>
#include "lazy_up.h"
#include "parse_exception.h"

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
    m_to_init.pop();
}

void removed_init_info_undo::undo() {
    m_to_init.push(m_info);
}


void lazy_up::propagate_to(modal_tree_node* new_world, unsigned relation) {
    SASSERT(!new_world->is_root());
    modal_tree_node* parent = new_world->get_parent();
    if (relation >= parent->get_spread_relation_cnt())
        return;
    for (const auto& box : parent->get_spread(relation)) {
        expr e = box.m_template->initialize(new_world->world_constant(), true);
        z3::expr_vector arg(ctx());
        arg.push_back(new_world->aux_predicate()); // actually negation; translated internally
        arg.push_back(box.m_justification);
        this->propagate(arg, e);
        LOG("Propagating (SP): " << !new_world->aux_predicate() << " && " << box.m_justification << " => " << e);
    }
}

void lazy_up::propagate_from(syntax_tree_node* temp, modal_tree_node* parent, unsigned relation, const expr& justification) {
    if (relation >= parent->get_child_relations_cnt())
        return;
    for (const auto& child : parent->get_children(relation)) {
        expr e = temp->initialize(child->world_constant(), true);
        z3::expr_vector arg(ctx());
        arg.push_back(child->aux_predicate()); // actually negation; translated internally
        arg.push_back(justification);
        this->propagate(arg, e);
        LOG("Propagating (SP): " << !child->aux_predicate() << " && " << justification  << " => " << e);
    }
}

unsigned lazy_up::get_variable(const func_decl& decl) {
    auto it = m_uf_to_id.find(decl);
    SASSERT(it != m_uf_to_id.end());
    return it->second;
}

expr lazy_up::create_formula(const expr& e) {
    std::stack<expr_info> expr_to_process;
    std::stack<expr_info> modals_to_process;
    expr_info info(e);

    m_syntax_tree = new syntax_tree(this);
    info.world = m_syntax_tree->get_root();

    modals_to_process.push(info);

    while (!modals_to_process.empty()) {
        info = modals_to_process.top();
        expr_to_process.push(info);
        modals_to_process.pop();

        SASSERT(m_processed_args.empty());
        SASSERT(m_apply_list.empty());
        m_processed_args.push({});


        while (!expr_to_process.empty()) {
            expr_info current = expr_to_process.top();
            expr_to_process.pop();

            VERIFY(current.e.is_app());
            LOG("Parsing (2): " << current.e);

            if (is_modal(current.decl)) {
                SASSERT(z3::eq(current.decl, m_box_decl));
                syntax_tree_node* existing;
                if ((existing = current.world->get_child(current.e)) == nullptr) {

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
                    SASSERT(!m_uf_to_id.contains(new_node->get_aux().decl()));
                    m_uf_to_id[new_node->get_aux().decl()] = m_uf_to_id.size();
                    LOG("Adding: " << new_node->get_aux().decl().name().str());

                    current.world = new_node;
                    LOG("New potential world: " << new_node->get_id() << " with parent " << (new_node->is_root() ? " root " : std::to_string(new_node->get_parent()->get_id())));
                    current.e = current.e.arg(1);
                    current.decl = current.e.decl();
                    current.arity = current.e.num_args();
                    LOG("Pushing: " << current.e.to_string());
                    modals_to_process.push(current);
                }
                else
                    current.world = existing;

                m_processed_args.top().push_back(current.world->get_aux());
            }
            else {
                for (unsigned i = current.e.num_args(); i > 0; i--) {
                    expr_info info2(current.e.arg(i - 1));
                    info2.world = current.world;
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

                if (app.decl.decl_kind() == Z3_OP_UNINTERPRETED && !z3::eq(app.decl.range(), m_world_sort) && !z3::eq(app.decl.range(), m_reachability_sort)) {
                    // for now: always flexible interpretation
                    sort_vector domain(m_ctx);
                    for (const z3::expr& arg : args)
                        domain.push_back(arg.get_sort());
                    //domain.push_back(m_world_sort);
                    if (!args.empty() && z3::eq(args[0].get_sort(), m_world_sort)) {
                        if (!z3::eq(args[0], m_placeholder))
                            throw parse_exception("Currently not supporting ABox/complex world terms: " + args.to_string());
                        //args.push_back(z3::expr(ctx(), Z3_mk_bound(ctx(), 0, get_world_sort())));
                        auto ast = (z3::ast)z3::expr(ctx(), Z3_mk_bound(ctx(), 0, get_world_sort()));
                        args.set(0, ast); // replace by placeholder
                    }
                    bool is_up = app.decl.range().is_bool() || app.decl.range().is_bv();
                    func_decl new_func = is_up
                            ? m_ctx.user_propagate_function(app.decl.name(), domain, app.decl.range())
                            : m_ctx.function(app.decl.name(), domain, app.decl.range());

                    m_processed_args.top().push_back(new_func(args));
                    if (!m_uf_set.contains(new_func)) {
                        LOG("Adding: " << new_func.name().str());
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
    return m_modal_tree->get_root()->get_syntax_node()->initialize(m_modal_tree->get_root()->world_constant(), true);
}

void lazy_up::push() {
    m_trail_sz.push_back(m_trail.size());
}

void lazy_up::pop(unsigned num_scopes) {
    SASSERT(m_trail_sz.size() >= num_scopes);
    unsigned old_sz = m_trail_sz[m_trail_sz.size() - num_scopes];
    m_trail_sz.resize(m_trail_sz.size() - num_scopes);
    while (m_trail.size() > old_sz) {
        undo_trail* trail = m_trail.top();
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
    expr arg = e.arg(func.arity() - 1);
    SASSERT(z3::eq(arg.get_sort(), m_world_sort));
    modal_tree_node* world = m_modal_tree->get(arg);
    unsigned var = get_variable(e.decl());
    world->assign(var, v);
    m_trail.push(new assignment_undo(world, var));

    syntax_tree_node* abs = m_syntax_tree->get_node(func);
    if (abs) { // Modal operator; otw. just ordinary predicate
        m_trail.push(new added_init_info_undo(m_to_init));
        m_to_init.push(init_info(abs, world, e, v));
    }
}

void lazy_up::final() {

    // TODO: First negative; then positive [performance reasons] (we then now already where to spread to)
    while (!m_to_init.empty()) {
        const auto& to_init = m_to_init.top();
        m_trail.push(new removed_init_info_undo(m_to_init, to_init));
        m_to_init.pop();
        const unsigned relation = to_init.m_template->get_relation();
        if (!to_init.m_positive) {
            modal_tree_node* new_world = m_modal_tree->create_node(to_init.m_template, to_init.m_parent, relation, to_init.m_justification);
            m_trail.push(new create_world_undo(m_modal_tree, relation));
            z3::expr inst = to_init.m_template->initialize(new_world->world_constant(), false);
            z3::expr_vector just(ctx());
            just.push_back(to_init.m_justification); // actually negation; translated internally
            this->propagate(just, inst);
            LOG("Propagating (SK): " << !to_init.m_justification << " => " << inst);
            propagate_to(new_world, relation);
        }
        else {
            spread_info info(to_init.m_template, to_init.m_justification);
            to_init.m_parent->add_spread(info, to_init.m_template->get_relation());
            m_trail.push(new add_spread_info_undo(to_init.m_parent, relation));
            propagate_from(to_init.m_template, to_init.m_parent, relation, to_init.m_justification);
        }
    }
}

void lazy_up::created(const expr& e) {
    LOG("Encountered: " << e);
}

void lazy_up::output_model(const model& model, std::ostream& ostream) {

    unsigned ri = 0;
    for (const auto& r : m_relation_list) {
        ostream << "Relation " << r.name().str() << ":\n";
        for (modal_tree_node* n : m_modal_tree->get_worlds()) {
            if (n->get_child_relations_cnt() <= ri)
                continue;
            for (modal_tree_node* child : n->get_children(ri))
                ostream << "\tw" << n->get_id() << " -> w" << child->get_id() << "\n";
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
            for (modal_tree_node* n : m_modal_tree->get_worlds()) {
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
