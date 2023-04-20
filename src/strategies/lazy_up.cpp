#include <algorithm>
#include <cstring>
#include "lazy_up.h"
#include "parse_exception.h"

#define ERROR_ABOX throw parse_exception("ABoxes have to be of the form \"global((x = w1 || ... |x = wn) => F)\"")

std::ostream& operator<<(std::ostream& os, undo_trail* undo) {
    undo->output(os);
    return os;
}

void assignment_undo::undo() {
    m_world->unassign(m_var);
}

bool new_spread_update::apply() {
    if (m_parent->is_blocked()) // For performance reasons
        return false;
    const unsigned relation = m_template->get_relation();
    spread_info info(m_template, m_justifications);
    m_parent->add_spread(info, relation);
    m_up->propagate_from(m_template, m_parent, relation, m_justifications);
    return true;
}

void new_spread_update::undo() {
    m_parent->remove_last_spread(m_template->get_relation());
}

void new_spread_update::output(std::ostream & os) {
    os << "that a" << m_template->get_id() << " will spread to all children of " << m_parent->world_constant() << " via relation r" << m_template->get_relation();
}

bool new_world_update::apply() {
    if (m_parent->is_blocked()) 
        return false;
    const unsigned relation = m_template->get_relation();
    modal_tree_node* new_world = m_up->m_modal_tree->get_or_create_node(m_template, m_parent, m_justifications);
    if (m_template->is_template_false()) {
        LOG("Propagating (SK): No propagation required; body trivial");
    }
    else {
        z3::expr inst = m_template->instantiate(new_world->world_constant(), false);
        m_up->propagate(m_justifications, inst);
        LOG("Propagating (SK): " << m_justifications << " => " << inst);
    }
    m_up->propagate_to(new_world, relation);
    m_up->apply_unconstrained(new_world);
    m_created = new_world;
    return true;
}

void new_world_update::undo() {
    SASSERT(m_created);
    SASSERT(m_created->get_parent_connection().m_from == m_parent);
    m_parent->remove_child(m_created, m_template->get_relation());
    m_up->m_modal_tree->remove_world(m_created);
}

void new_world_update::output(std::ostream & os) {
    if (!m_created) {
        os << "will create world reachable from " << m_parent->world_constant() << " via relation r" << m_template->get_relation();
        return;
    }
    os << "created world " <<  m_created->world_constant() << " with justification " << m_created->justification() << " reachable from " << m_parent->world_constant() << " via relation r" << m_template->get_relation();
}

bool connect_worlds_update::apply() {
    if (!m_connection.m_from->add_named_child(m_connection, m_relation))
        return true; // There is nothing to do; they are already connected (e.g., ABox + transitivity both added that edge)
    m_to_undo.push_back(m_connection);
    m_up->propagate_to(m_connection, m_relation);
    if (!m_up->m_relation_trans[m_relation])
        return true;

    // TODO: For more complicated ALC extensions we might need to call this for every Diamond (unnamed worlds) as well
    // Assumption: The parent and the child are already transitive. We only have to process the direct predecessors/successors

    if (m_connection.m_from->get_parent_relations_cnt() > m_relation) {
        const std::vector<connection_info>& ingoing = m_connection.m_from->get_parents(m_relation);
        for (unsigned i = 0 ; i < ingoing.size(); i++) {
            const auto& in = ingoing[i].m_from;
            if (!in->is_named())
                continue;
            z3::expr_vector just(m_up->ctx());
            for (const auto& j : ingoing[i].m_justifications) {
                just.push_back(j);
            }
            for (const auto& j : m_connection.m_justifications) {
                just.push_back(j);
            }
            LOG("Propagating (tran): " << just << " => " << m_up->create_reachable(m_up->m_relation_list[m_relation](), in->world_constant(), m_connection.m_to->world_constant()));
            m_up->propagate(just, m_up->create_reachable(m_up->m_relation_list[m_relation](), in->world_constant(), m_connection.m_to->world_constant()));
        }
    }
    if (m_connection.m_to->get_child_relations_cnt() > m_relation) {
        const std::vector<connection_info>& outgoing = m_connection.m_to->get_children(m_relation);
        for (unsigned i = 0 ; i < outgoing.size(); i++) {
            const auto& out = outgoing[i].m_to;
            if (!out->is_named())
                continue;
            z3::expr_vector just(m_up->ctx());
            for (const auto& j : m_connection.m_justifications) {
                just.push_back(j);
            }
            for (const auto& j : outgoing[i].m_justifications) {
                just.push_back(j);
            }
            // TODO: We could add the connection directly. However, then only the UP is aware of the connection
            //  e.g., (reachable w1 w2) & (reachable w2 w3) & (not (reachable w1 w3))
            //  Who should detect this conflict? If we propagate Z3 can do this; otw. we have to do it.
            //  for now, we do it. Later we can take care of this on our own
            LOG("Propagating (tran): " << just << " => " << m_up->create_reachable(m_up->m_relation_list[m_relation](), m_connection.m_from->world_constant(), out->world_constant()));
            m_up->propagate(just, m_up->create_reachable(m_up->m_relation_list[m_relation](), m_connection.m_from->world_constant(), out->world_constant()));
            // connection_info connection(in, out, just);
            // in->add_named_child(connection, m_relation);
        }
    }
    return true;
}

void connect_worlds_update::undo() {
    m_connection.m_from->remove_child(m_connection.m_to, m_relation);
}

void connect_worlds_update::output(std::ostream& os) {
    os << "connected named world " << m_connection.m_from->world_constant() << " with world " << m_connection.m_to->world_constant() << " with relation r" << m_relation;
}

void added_graph_update_undo::undo() {
    SASSERT(!m_pending_updates.empty());
    m_pending_updates.remove(m_added);
    SASSERT(!m_pending_updates.contains(m_added));
    delete m_added;
    m_added = nullptr;
}

void removed_graph_update_undo::undo() {
    m_removed->undo();
    m_pending_updates.add(m_removed);
}

void log_clause(expr const& proof, expr_vector const& clause) {
    //LOG("Proof: " << proof);
    //LOG("Clause: " << clause);
}

void lazy_up::propagate_to(modal_tree_node* new_world, unsigned relation) {
     SASSERT(!new_world->is_root());
    propagate_to(new_world->get_parent_connection(), relation);
}

void lazy_up::propagate_to(const connection_info& connection, unsigned relation) {
    SASSERT(connection.m_from);
    SASSERT(connection.m_to);
    modal_tree_node* from = connection.m_from;
    if (relation >= from->get_spread_relation_cnt())
        return;
    modal_tree_node* to = connection.m_to;
    for (const auto& box : from->get_spread(relation)) {
        expr e = box.m_template->instantiate(to->world_constant(), true);
        expr_vector just(ctx());
        for (const auto& j : connection.m_justifications)
            just.push_back(j);
        for (const auto& j : box.m_justifications)
            just.push_back(j);
        LOG("Propagating (SP): " << just << " => " << e);
        propagate(just, e);
        if (m_relation_trans[relation]) {
            LOG("Propagating (SP+trans): " << just << " => " << box.m_template->get_aux().decl()(connection.m_to->world_constant()));
            propagate(just, box.m_template->get_aux().decl()(connection.m_to->world_constant()));
        }
    }
}

void lazy_up::propagate_from(syntax_tree_node* temp, modal_tree_node* parent, unsigned relation, const expr_vector& justifications) {
    if (relation >= parent->get_child_relations_cnt())
        return;
    for (const connection_info& connection : parent->get_children(relation)) {
        expr e = temp->instantiate(connection.m_to->world_constant(), true);
        expr_vector just(ctx());
        for (const auto& j : connection.m_justifications)
            just.push_back(j);
        for (const auto& j : justifications)
            just.push_back(j);
        LOG("Propagating (SP): " << just  << " => " << e);
        propagate(just, e);
        if (m_relation_trans[relation]) {
            LOG("Propagating (SP+trans): " << just << " => " << temp->get_aux().decl()(connection.m_to->world_constant()));
            propagate(just, temp->get_aux().decl()(connection.m_to->world_constant()));
        }
    }
}

void lazy_up::apply_unconstrained(modal_tree_node* world) {
    for (syntax_tree_node* n : m_global) {
        LOG("Unconditional constraint: " + n->get_template(true).to_string() + " to world " + world->world_constant().to_string());
        propagate(world->justification(), n->instantiate(world->world_constant(), true));
    }
}

unsigned lazy_up::get_or_add_relation(const expr& relation) {
    if (!relation.is_const())
        throw parse_exception("Relations have to be constants unlike " + relation.to_string());
    if (!m_relation_to_id.contains(relation.decl())) {
        unsigned relation_id = m_relation_to_id.size();
        m_relation_to_id[relation.decl()] = relation_id;
        m_relation_list.push_back(relation.decl());
        m_relation_trans.push_back(false);
        LOG("Introduced relation: " << relation << " with id " << relation_id);
        return relation_id;
    }
    else
        return m_relation_to_id[relation.decl()];
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

void lazy_up::try_global_to_local() {
    unsigned i = 0;
    unsigned sz = m_global.size();
    while (i < sz) {
        if (try_apply_local(m_global[i]))
            m_global[i] = m_global[--sz];
        else
            i++;
    }
    // TODO: We could now delete the node in the syntax tree
    //  [However, this is not really easy because of the way the are stored (the id = position in the list) ...]

    m_global.resize(sz);
}

bool lazy_up::try_apply_local(syntax_tree_node* abs) {

    z3::expr e = abs->get_template(true);
    SASSERT(!e.is_implies());
#define ADD_WORLD(X) do {                                                                   \
                    e = (X);                                                                \
                    if (is_placeholder(e.arg(0).decl()) == is_placeholder(e.arg(1).decl())) \
                        ERROR_ABOX;                                                              \
                    if (is_placeholder(e.arg(0).decl()))                                    \
                        worlds.push_back(e.arg(1));                                         \
                    else                                                                    \
                        worlds.push_back(e.arg(0));                                         \
                    } while (false)

    LOG("Trying to convert global " << e << " to abox");

    if (!e.is_or() || e.num_args() < 2)
        return false;

    expr_vector worlds(m_ctx);
    expr_vector args = e.args();
    const unsigned sz = args.size();
    unsigned i = 0;
    for (; i < sz; i++) {
        expr arg = args[i];
        if (arg.is_not()) {
            arg = arg.arg(0);
            if (arg.is_eq()) {
                ADD_WORLD(arg);
                break;
            }
            else if (arg.is_or() && arg.arg(0).is_eq()) {
                ADD_WORLD(arg.arg(0));
                for (int j = 1; j < arg.num_args(); j++) {
                    if (!arg.arg(j).is_eq())
                        ERROR_ABOX;
                    ADD_WORLD(arg.arg(j));
                }
                break;
            }
        }
        else if (arg.is_and() && arg.arg(0).is_not() && arg.arg(0).arg(0).is_eq()) {
            worlds.push_back(arg.arg(0).arg(0));
            for (int j = 1; j < arg.num_args(); j++) {
                if (!arg.arg(j).is_not() || !arg.arg(j).arg(0).is_eq())
                    ERROR_ABOX;
                ADD_WORLD(arg.arg(j).arg(0));
            }
            break;
        }
    }

    if (i == args.size())
        return false;

    e = args[args.size() - 1];
    args.set(i, e);
    args.resize(args.size() - 1);
    abs->set_template(args.size() == 1 ? args[0] : z3::mk_or(args));

    if (get_logging()) {
        LOG("Extracted ABox " << abs->get_template(true) << " for ");
        for (const auto& w : worlds)
            LOG("World " << w);
    }

    for (const auto& w : worlds) {
        m_modal_tree->get_or_create_named_node(w);
        propagate(m_ctx.bool_val(true), abs->instantiate(w, true));
    }
    return true;
}

expr lazy_up::create_formula(const expr& e) {
    std::stack<expr_info> expr_to_process;
    std::stack<expr_info> subformulas_to_process;
    expr_info info(e);
    info.top_level = true;
    info.no_scope = true;

    m_syntax_tree = new syntax_tree(this);
    info.world = m_syntax_tree->get_root();

    delete m_modal_tree;
    m_modal_tree = new modal_tree(m_syntax_tree);

    subformulas_to_process.push(info);
    
    sort_vector domain(m_ctx);
    domain.push_back(m_decls.relation_sort);
    domain.push_back(m_decls.world_sort);
    domain.push_back(m_decls.world_sort);
    m_decls.reachable_uf = m_ctx.user_propagate_function(m_ctx.str_symbol("reachable"), domain, m_ctx.bool_sort());

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

                    unsigned relation_id = get_or_add_relation(current.e.arg(0));

                    syntax_tree_node* new_node = m_syntax_tree->create_node(current.world, relation_id, current.e);
                    SASSERT(get_variable(new_node->get_aux().decl()) == -1);
                    m_uf_to_id[new_node->get_aux().decl()] = m_uf_to_id.size();
                    LOG("Adding: " << new_node->get_aux().decl().name().str());

                    current.world = new_node;
                    LOG("New potential world: " << new_node->get_id() << " with parent " << (new_node->is_root() ? " root " : std::to_string(new_node->get_parent()->get_id())));
                    current.e = current.e.arg(1);
                    current.decl = current.e.decl();
                    current.arity = current.e.num_args();
                    current.top_level = false;
                    current.no_scope = false;
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
                expr constr = current.e.arg(0);
                current.e = constr;
                current.decl = constr.decl();
                current.arity = constr.num_args();
                current.top_level = false;
                current.no_scope = false;
                LOG("Global: " << constr.to_string());
                subformulas_to_process.push(current);
                add_global(new_node);
                m_processed_args.top().push_back(ctx().bool_val(true));
            }
            else if (is_trans(current.decl)) {
                if (!current.top_level)
                    throw parse_exception("\"trans\" may only occur top-level");
                m_relation_trans[get_or_add_relation(current.e.arg(0))] = true;
                m_processed_args.top().push_back(ctx().bool_val(true));
            }
            else {
                for (unsigned i = current.e.num_args(); i > 0; i--) {
                    expr_info info2(current.e.arg(i - 1));
                    info2.world = current.world;
                    info2.top_level = current.top_level && current.decl.decl_kind() == Z3_OP_AND;
                    info2.no_scope = current.no_scope;
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

                if (app.decl.decl_kind() == Z3_OP_UNINTERPRETED) {
                    if (is_reachable_extern(app.decl)) {
                        modal_tree_node* w1 = is_placeholder(args[1].decl()) ? m_modal_tree->get_root() : m_modal_tree->get_or_create_named_node(args[1]);
                        modal_tree_node* w2 = is_placeholder(args[2].decl()) ? m_modal_tree->get_root() : m_modal_tree->get_or_create_named_node(args[2]);
                        get_or_add_relation(args[0]);
                        m_processed_args.top().push_back(m_decls.reachable_uf(args));
                    }
                    else if (!is_world(app.decl.range()) && !is_relation(app.decl.range())) {
                        sort_vector domain(m_ctx);
                        for (const z3::expr& arg : args)
                            domain.push_back(arg.get_sort());
                        if (args.empty() || !is_world(args[0].get_sort())) {
                            // For now, we don't care about rigid functions. We don't even want to observe them
                            m_processed_args.top().push_back(m_ctx.function(app.decl.name(), domain, app.decl.range())(args));
                        }
                        else {
                            if (!app.no_scope && !is_placeholder(args[0].decl())) {
                                throw parse_exception("Non-\"world\" constants only outside of modal operators for now: " + current.e.to_string());
                            }
                            if (is_placeholder(args[0].decl())) {
                                z3::expr ast = z3::expr(ctx(), Z3_mk_bound(ctx(), 0, m_decls.world_sort));
                                args.set(0, ast);
                            }
                            else {
                                z3::expr ast = args[0];
                                args.set(0, ast);
                                m_modal_tree->get_or_create_named_node(ast);
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
                    }
                    else 
                        m_processed_args.top().push_back(app.decl(args));
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

    z3::expr assertion = m_modal_tree->get_root()->get_syntax_node()->instantiate(m_modal_tree->get_root()->world_constant(), true);
    m_assertions.push_back(assertion);
    try_global_to_local();
    for (modal_tree_node* existing : m_modal_tree->get_existing_worlds())
        apply_unconstrained(existing);

    return post_rewrite(z3::mk_and(m_assertions).decl(), m_assertions);
}

void lazy_up::push() {
    m_trail_sz.push_back(m_trail.size());
}

void lazy_up::pop(unsigned num_scopes) {
    // LOG("Undoing current state:\n" << *m_modal_tree << "\n");
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
    try {
        SASSERT(value.is_bool());
        bool v = value.is_true();
        LOG(e << " = " << value);
        func_decl func = e.decl();
        SASSERT(func.arity() > 0);
        if (is_reachable_intern(func)) {
            modal_tree_node* w1 = m_modal_tree->get_or_create_named_node(e.arg(1));
            modal_tree_node* w2 = m_modal_tree->get_or_create_named_node(e.arg(2));
            SASSERT(w1->is_named());
            SASSERT(w2->is_named());
            SASSERT(m_relation_to_id.contains(e.arg(0).decl()));
            // we will anyway not connect two named worlds automatically. We can ignore the negative case (the SAT core will deal with prop. conflicts)
            if (!v)
                return;
            unsigned relation_id = m_relation_to_id[e.arg(0).decl()];
            z3::expr_vector just(ctx());
            just.push_back(e);
            m_pending_updates.add(new connect_worlds_update(this, connection_info(w1, w2, just), relation_id));
            add_trail(new added_graph_update_undo(m_pending_updates, m_pending_updates.back()));
            return;
        }
        expr arg = e.arg(0);
        SASSERT(is_world(arg.get_sort()));
        modal_tree_node* world = m_modal_tree->get(arg);
        SASSERT(world);
        unsigned var = get_variable(e.decl());
        SASSERT(var != -1);
        //SASSERT(!world->is_assigned(var));
        world->assign(var, v);
        add_trail(new assignment_undo(world, var));
    
        syntax_tree_node* abs = m_syntax_tree->get_node(func);
        if (abs) { // Modal operator; otw. just ordinary predicate
            z3::expr_vector just(ctx());
            just.push_back(e);
            m_pending_updates.add(v ? (graph_update*)new new_spread_update(this, abs, world, just) : new new_world_update(this, abs, world, just));
            add_trail(new added_graph_update_undo(m_pending_updates, m_pending_updates.back()));
        }
    
        //if (m_trail_sz.empty()) // Root level; we won't have to revert them
        //    final();
    }
    catch (const exception& e) {
        if (strcmp(e.msg(), "canceled") != 0) {
            throw;
        }
    }
}

static int final_checks = 0;

void lazy_up::final() {
    try {
        if (m_trail_sz.empty())
            LOG("Eager check: " << ++final_checks);
        else
            LOG("Final check: " << ++final_checks);
        // LOG("Current state: " << *m_modal_tree);
        unsigned i = 0;
        while (i < m_pending_updates.size()) {
            graph_update* to_apply = m_pending_updates[i];
            if (to_apply->apply()) {
                add_trail(new removed_graph_update_undo(m_pending_updates, to_apply));
                m_pending_updates.remove_at(i);
            }
            else
                i++;
        }
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
    std::vector<std::string> name_list;
    std::unordered_set<std::string> name_set;
    std::unordered_map<modal_tree_node*, std::string> world_to_name;
    
    // Find names
    for (const auto& w : m_modal_tree->get_existing_worlds()) {
        if (w->is_named()) {
            std::string name = w->world_constant().decl().name().str();
            name_set.insert(name);
            name_list.push_back(name);
            world_to_name[w] = name;
        }
    }
    unsigned last_name = 0;
    for (const auto& w : m_modal_tree->get_existing_worlds()) {
        if (!w->is_named()) {
            std::string name;
            do {
                name = "w" + std::to_string(last_name++);
            } while (name_set.contains(name));
            name_set.insert(name);
            name_list.push_back(name);
            world_to_name[w] = name;
        }
    }

    ostream << "Worlds:\n\n";
    ostream << name_list[0];
    for (unsigned i = 1; i < name_list.size(); i++) {
        ostream << ", " << name_list[i];
    }
    ostream << "\n\n";
    
    for (const auto& r : m_relation_list) {
        ostream << "Relation " << r.name().str() << ":\n";
        for (modal_tree_node* n : m_modal_tree->get_existing_worlds()) {
            if (n->get_child_relations_cnt() <= ri)
                continue;
            for (const connection_info& connection : n->get_children(ri))
                ostream << "\t" << world_to_name.at(n) << " -> " << world_to_name.at(connection.m_to) << "\n";
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
                        ostream << "\t" << world_to_name.at(n) << ": " << (val == Z3_L_TRUE ? "true" : "false") << "\n";
                }
                else {
                    expr eval = model.eval(uf(n->world_constant()), true);
                    ostream << "\t" << world_to_name.at(n) << ": " << eval << "\n";
                }
            }
            ostream << "\n";
        }
    }
    ostream << "Non-Modal functions:\n";
    unsigned sz = model.num_consts();
    for (unsigned i = 0; i < sz; i++) {
        z3::func_decl f = model.get_const_decl(i);
        if (!is_world(f.range()) && !is_relation(f.range()))
            ostream << f << ": " << model.get_const_interp(f) << "\n";
    }
    sz = model.num_funcs();
    for (unsigned i = 0; i < sz; i++) {
        z3::func_decl f = model.get_func_decl(i);
        if (!is_world(f.range()) && !is_relation(f.range()) && (f.arity() == 0 || is_world(f.domain(0))))
            ostream << f << ": " << model.get_func_interp(f) << "\n";
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
        bool ml = is_modal(f);
        bool global = is_global(f);
        bool reachable = is_reachable_extern(f);
        unsigned relation_id;

        LOG("Checking " << current.original_expr << " with arg " << current.processed_idx);
        
        if (is_trans(f)) {
            to_process.pop();
            std::vector<std::vector<bool>> reachability_matrix;
            std::vector<unsigned> reachable_cnt;
            std::vector<modal_tree_node*> nodes = m_modal_tree->get_existing_worlds();
            unsigned i;

            relation_id = get_or_add_relation(current.original_expr.arg(0));
            LOG("Checking transitivity of relation " << current.original_expr.arg(0) << " with id: " << relation_id);
            const unsigned sz = nodes.size();
            for (i = 0; i < sz; i++) {
                reachability_matrix.emplace_back().resize(sz);
                if (nodes[i]->get_child_relations_cnt() <= relation_id)
                    continue;
                for (const auto& child : nodes[i]->get_children(relation_id)) {
                    reachability_matrix[i][child.m_to->get_internal_idx()] = true;
                }
            }
            // for now do the inefficient O(n^3) approach (compare neighbors with cg):
            for (i = 0; i < sz; i++)
                for (unsigned j = 0; j < sz; j++)
                    for (unsigned k = 0; k < sz; k++)
                        reachability_matrix[j][k] = reachability_matrix[j][k] || (reachability_matrix[j][i] && reachability_matrix[i][k]);
            
            reachable_cnt.resize(sz);
            for (i = 0; i < sz; i++) {
                for (unsigned j = 0; j < sz; j++) {
                    reachable_cnt[i] += reachability_matrix[i][j];
                }
            }

            for (i = 0; i < sz; i++) {
                if ((nodes[i]->get_child_relations_cnt() <= relation_id ? 0 : nodes[i]->get_children(relation_id).size()) != reachable_cnt[i])
                    break;
            }
            to_process.top().args.push_back(m_ctx.bool_val(i == sz));
            continue;
        }
        else if (!ml && !global && !reachable && kind == Z3_OP_UNINTERPRETED) {
            // Prop. variables
            to_process.pop();
            if (current.original_expr.num_args() > 0 && is_world(f.domain(0))) {
                if (m_orig_uf_to_new_uf.contains(f)) {
                    unsigned vid = get_variable(*(m_orig_uf_to_new_uf[f]));
                    SASSERT(vid != -1);
                    modal_tree_node* w = current.world;
                    if (!is_placeholder(current.original_expr.arg(0).decl())) {
                        w = m_modal_tree->get(current.original_expr.arg(0));
                        SASSERT(w);
                    }
                    if (!w->is_assigned(vid)) {
                        //to_process.top().args.push_back(current.original_expr);
                        to_process.top().args.push_back(m_ctx.bool_val(false)); // completion to please MC
                    }
                    else {
                        to_process.top().args.push_back(ctx().bool_val(w->get_assignment(vid) == Z3_L_TRUE));
                    }
                }
                else {
                    to_process.top().args.push_back(m_ctx.bool_val(false)); // the preprocessor might have remove whole declarations
                }
            }
            else {
                to_process.top().args.push_back(m.eval(current.original_expr, true)); // completion to please MC
            }
            continue;
        }
        else if (kind == Z3_OP_EQ && is_world(current.original_expr.arg(0).decl().range())) {
            to_process.pop();
            z3::expr lhs = current.original_expr.arg(0);
            z3::expr rhs = current.original_expr.arg(1);
            if (is_placeholder(lhs.decl()) == is_placeholder(rhs.decl())) {
                ERROR_ABOX;
            }
            to_process.top().args.push_back(m_ctx.bool_val(z3::eq(current.world->world_constant(), is_placeholder(lhs.decl()) ? rhs : lhs)));
            continue;
        }
        else if (reachable) {
            to_process.pop();
            modal_tree_node* w1 = current.world;
            modal_tree_node* w2 = current.world;
            if (!is_placeholder(current.original_expr.arg(1).decl()))
                w1 = m_modal_tree->get(current.original_expr.arg(1));
            if (!is_placeholder(current.original_expr.arg(2).decl()))
                w2 = m_modal_tree->get(current.original_expr.arg(2));
            if (!m_relation_to_id.contains(current.original_expr.arg(0).decl())) {
                to_process.top().args.push_back(m_ctx.bool_val(false));
                continue;
            }
            unsigned relation = m_relation_to_id[current.original_expr.arg(0).decl()];
            if (w1->get_child_relations_cnt() <= relation) {
                to_process.top().args.push_back(m_ctx.bool_val(false));
                continue;
            }
            bool found = false;
            for (const connection_info& connections : w1->get_children(relation)) {
                if (connections.m_to == w2) {
                    found = true;
                    break;
                }
            }
            to_process.top().args.push_back(m_ctx.bool_val(found));
            continue;
        }
        
        unsigned max;
        if (ml) {
            relation_id = m_relation_to_id.contains(current.original_expr.arg(0).decl()) 
                    ? m_relation_to_id[current.original_expr.arg(0).decl()]
                    : -1; // the relation might be optimized away. Hence, there are no such children
            max = current.world->get_child_relations_cnt() > relation_id ? current.world->get_children(relation_id).size() : 0;
        }
        else if (global) {
            max = m_modal_tree->existing_size();
        }
        else {
            max = current.original_expr.num_args();
        }
        
        if (!current.args.empty()) {
            if (kind == Z3_OP_AND || (ml && is_box(f)) || global) {
                if (to_process.top().args.back().is_false()) {
                    to_process.pop();
                    to_process.top().args.push_back(ctx().bool_val(false));
                    continue;
                }
            }
            else if (kind == Z3_OP_OR || (ml && is_dia(f))) {
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
            bool failed = false;
            
            if (kind == Z3_OP_AND || is_box(f) || is_global(f)) {
                for (const auto& arg : args) {
                    SASSERT(!arg.is_false()); // otw. we would have detected earlier
                    if (!arg.is_true()) {
                        failed = true;
                        break;
                    }
                }
                if (!failed)
                    to_process.top().args.push_back(ctx().bool_val(true));
                else 
                    to_process.top().args.push_back(m.eval(current.original_expr, true));
            }
            else if (kind == Z3_OP_OR || is_dia(f)) {
                for (const auto& arg : args) {
                    SASSERT(!arg.is_true()); // otw. we would have detected earlier
                    if (!arg.is_false()) {
                        failed = true;
                        break;
                    }
                }
                if (!failed)
                    to_process.top().args.push_back(ctx().bool_val(false));
                else
                    to_process.top().args.push_back(m.eval(current.original_expr, true));
            }
            else if (kind == Z3_OP_NOT) {
                SASSERT(args.size() == 1);
                if (args[0].is_true())
                    to_process.top().args.push_back(ctx().bool_val(false));
                else if (args[0].is_false())
                    to_process.top().args.push_back(ctx().bool_val(true));
                else
                    to_process.top().args.push_back(m.eval(current.original_expr, true));
            }
            else if (kind == Z3_OP_IMPLIES) {
                SASSERT(args.size() == 2);
                SASSERT(!args[0].is_false()); // otw. we would have detected earlier
                SASSERT(!args[1].is_true());
                if (args[0].is_true() && args[1].is_false())
                    to_process.top().args.push_back(ctx().bool_val(false));
                else
                    to_process.top().args.push_back(m.eval(current.original_expr, true));
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
                    to_process.top().args.push_back(m.eval(current.original_expr, true));;
            }
            else 
                to_process.top().args.push_back(m.eval(current.original_expr, true));;
            continue;
        }
        
        if (ml) {
            to_process.push({ current.world->get_children(relation_id)[to_process.top().processed_idx++].m_to, current.original_expr.arg(1) });
        }
        else if (global) {
            // TODO: Try to extract ABox here as well for performance reasons...
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

#undef ERROR_ABOX
