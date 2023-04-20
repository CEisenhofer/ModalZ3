#pragma once

#include <algorithm>
#include "modal_tree.h"


modal_tree_node* get_from::operator()(const connection_info& c) const {
    return c.m_from;
}

modal_tree_node* get_to::operator()(const connection_info& c) const {
    return c.m_to;
}

bool modal_tree_node::is_assigned(unsigned int variable) const {
    return m_assignment_set.size() > variable && m_assignment_set[variable] != Z3_L_UNDEF;
}

Z3_lbool modal_tree_node::get_assignment(unsigned int variable) const {
    if (m_assignment_set.size() <= variable)
        return Z3_L_UNDEF;
    return m_assignment_set[variable];
}

void modal_tree_node::unassign(unsigned int variable) {
    SASSERT(is_assigned(variable));
    assign(variable, Z3_L_UNDEF);
}

void modal_tree_node::assign(unsigned int variable, bool val) {
    assign(variable, val ? Z3_L_TRUE : Z3_L_FALSE);
}
void modal_tree_node::assign(unsigned int variable, Z3_lbool val) {
    if (m_assignment_set.size() <= variable) {
        m_assignment_set.resize(variable + 1);
    }
    if (val == Z3_L_UNDEF) {
        m_assignment_set[variable] = Z3_L_UNDEF;
        SASSERT(!m_assignment_list.empty());
        SASSERT(m_assignment_list.back() == variable);
        // Otw. if we need non-chronological: the set contains additionally the index to the variable in the list
        // We swap this element with the last element in the list and change the index for the last element accordingly
        m_assignment_list.pop_back();
        return;
    }
    m_assignment_set[variable] = val;
    m_assignment_list.push_back(variable);
}

void modal_tree_node::add_spread(const spread_info & info, unsigned int relation) {
    if (m_spread.size() <= relation)
        m_spread.resize(relation + 1);
    m_spread[relation].push_back(info);
}

void modal_tree_node::add_skolem_child(modal_tree_node* node, syntax_tree_node* abs) {
    unsigned relation = abs->get_relation();
    add_named_child({ this, node, node->justification() }, relation);

    unsigned id = abs->get_id();
    if (m_created_children.size() <= id)
        m_created_children.resize(id + 1);
    m_created_children[id] = node;
}

bool modal_tree_node::add_named_child(const connection_info& connection, unsigned relation) {
    if (m_existing_children.size() <= relation)
        m_existing_children.resize(relation + 1);
    SASSERT(connection.m_from == this);
    if (!m_existing_children[relation].add(connection)) {
        SASSERT(connection.m_to->m_existing_parents.size() > relation && connection.m_to->m_existing_parents[relation].contains(connection.m_to));
        return false;
    }
    SASSERT(connection.m_to->m_existing_parents.size() <= relation || !connection.m_to->m_existing_parents[relation].contains(connection.m_to));

    if (connection.m_to->m_existing_parents.size() <= relation)
        connection.m_to->m_existing_parents.resize(relation + 1);
    bool added = connection.m_to->m_existing_parents[relation].add(connection);
    SASSERT(added);
    return true;
}

modal_tree_node* modal_tree_node::get_created_child(syntax_tree_node* abs) {
    unsigned id = abs->get_id();
    if (id >= m_created_children.size())
        return nullptr;
    return m_created_children[id];
}

void modal_tree_node::remove_child(modal_tree_node* child, unsigned relation) {
    SASSERT(m_existing_children.size() >= relation);
    SASSERT(child->m_existing_parents.size() >= relation);
    m_existing_children[relation].remove(child);
    child->m_existing_parents[relation].remove(this);
}

void modal_tree_node::remove_last_spread(unsigned relation) {
    SASSERT(m_spread.size() >= relation);
    SASSERT(!m_spread[relation].empty());
    m_spread[relation].pop_back();
}

bool modal_tree_node::is_blocked() {
    modal_tree_node* parent = this;
    while ((parent = parent->get_parent_connection().m_from) != nullptr) {
        // subset
        if (parent->is_named())
            goto failed; // for safety. There might be constraints like reachable(w1, w2) we do not detect by subset check
            
        for (unsigned v : this->m_assignment_list) {
            Z3_lbool tval = this->get_assignment(v);
            if (tval != Z3_L_UNDEF) {
                if (tval != parent->get_assignment(v))
                    goto failed;
            }
        }
        m_blocked_by = parent;
        return true;
        failed:
        ;
    }
    return false;
}

std::ostream& operator<<(std::ostream & os, const modal_tree_node & w) {
    os << "**World " << w.world_constant() << "**:\n"
       << "Aux: " << w.justification() << "\n"
       << "Parent: " << (w.get_parent_connection().m_from == nullptr ? "null" : w.get_parent_connection().m_from->world_constant().to_string()) << "\n";
    if (w.get_syntax_node()) {
        os << "Abstract: a" << w.get_syntax_node()->get_id() << "\n"
           << "Template: " << w.get_syntax_node()->get_template(false) << "\n";
    }
    os << "\nReachable: \n";
    for (unsigned r = 0; r < w.get_child_relations_cnt(); r++) {
        for (const auto& reachable : w.get_children(r)) {
            os << "via r" << r << ": " << reachable.m_to->world_constant() << " [" << reachable.m_justifications << "]\n";
        }
    }
    os << "\nSpread: \n";
    for (unsigned r = 0; r < w.get_spread_relation_cnt(); r++) {
        for (const auto& spread : w.get_spread(r)) {
            os << "via r" << r << ": a" << spread.m_template->get_id() << " [" << spread.m_justifications << "] Templ.: "
               << spread.m_template->get_template(true) << "\n";
        }
    }
    os << "\nAssignment: \n";
    for (unsigned v = 0; v < w.get_assignment_cnt(); v++) {
        if (w.is_assigned(v)) {
            os << "v" << v << ": " << (w.get_assignment(v) == Z3_L_TRUE ? "1" : "0") << "\n";
        }
    }
    return os;
}

modal_tree_node* modal_tree::get_or_create_node(syntax_tree_node* abs, modal_tree_node* parent, const z3::expr_vector& justification, z3::expr world_constant) {
    modal_tree_node* node;
    if (parent && (node = parent->get_created_child(abs))) {
        node->m_skolem_info.m_justifications = justification;
        LOG("Recreated: " << node->world_constant() << " with justification " << node->justification());
        node->m_idx = m_existing_nodes.size();
    }
    else {
        bool named = (z3::ast)world_constant;
        if (!named)
            world_constant = z3::expr(m_ctx, Z3_mk_fresh_const(m_ctx, "world", get_world_sort()));
        node = new modal_tree_node(existing_size(), named, abs, parent, world_constant, justification);
        LOG("Created world " << node->world_constant() << " with aux " << node->justification());
        m_expr_to_node[world_constant] = node;
        m_actual_nodes.push_back(node);
    }
    if (parent)
        parent->add_skolem_child(node, abs);
    m_existing_nodes.push_back(node);
    return node;
}

void modal_tree::remove_world(modal_tree_node* world) {
#if 0 and not defined NDEBUG
    // this is weird but may happen unfortunately. (Not necessarily a bug):
    // the solver may reinitialize some of the auxiliary variables and assign them.
    // Therefore, a non-existing world has some children. We just ignore this
    //
    // we first have to detach all children/parents
    for (const auto& c : world->m_existing_children) {
        SASSERT(c.empty());
    }
    for (const auto& c : world->m_existing_parents) {
        SASSERT(c.empty());
    }
#endif
    SASSERT(m_existing_nodes.size() > world->m_idx && world == m_existing_nodes[world->m_idx]);
    m_existing_nodes.back()->m_idx = world->m_idx;
    m_existing_nodes[world->m_idx] = m_existing_nodes.back();
    m_existing_nodes.pop_back();
}

void modal_tree::remove_blocked() {
    unsigned i = 0;
    unsigned last = m_existing_nodes.size();
    while (i < last) {
        if (m_existing_nodes[i]->blocked_by() != nullptr) {
            SASSERT(!m_existing_nodes[i]->is_named());
            auto& parent = m_existing_nodes[i]->get_parent_connection();
            SASSERT(parent.m_from && parent.m_from->blocked_by() == nullptr);
            parent.m_from->remove_child(parent.m_to, parent.m_to->get_syntax_node()->get_relation());
            parent.m_from->add_named_child(
                    connection_info(parent.m_from, parent.m_to->blocked_by(), parent.m_justifications),
                    parent.m_to->get_syntax_node()->get_relation());
            m_existing_nodes[i] = m_existing_nodes[--last];
            continue;
        }
        i++;
    }
    m_existing_nodes.resize(last);
}

void modal_tree::transitive_closure(unsigned relation_id) {
    std::vector<std::vector<bool>> reachable;

    const unsigned sz = m_existing_nodes.size();
    for (unsigned i = 0; i < sz; i++) {
        reachable.emplace_back().resize(sz);
        if (m_existing_nodes[i]->get_child_relations_cnt() <= relation_id)
            continue;
        for (const auto& child : m_existing_nodes[i]->get_children(relation_id)) {
            reachable[i][child.m_to->get_internal_idx()] = true;
        }
    }

    // for now do the inefficient O(n^3) approach (compare neighbors with cg):
    for (unsigned i = 0; i < sz; i++)
        for (unsigned j = 0; j < sz; j++)
            for (unsigned k = 0; k < sz; k++) {
                if (!reachable[j][k] && reachable[j][i] && reachable[i][k]) {
                    auto from = m_existing_nodes[j];
                    auto to = m_existing_nodes[k];
                    bool added = from->add_named_child(connection_info(from, to, z3::expr_vector(m_ctx)), relation_id);
                    SASSERT(added);
                    reachable[j][k] = true;
                }
            }
}

std::ostream& operator<<(std::ostream& os, const modal_tree& m) {
    for (const auto& w : m.get_existing_worlds()) {
        os << *w << "\n";
    }
    return os;
}
