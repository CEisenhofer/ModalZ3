#pragma once

#include "modal_tree.h"

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

const spread_info& modal_tree_node::last_spread(unsigned int relation) const {
    SASSERT(m_spread.size() >= relation);
    SASSERT(!m_spread[relation].empty());
    return m_spread[relation].back();
}

void modal_tree_node::add_child(modal_tree_node *node, syntax_tree_node *abs) {
    unsigned relation = abs->get_relation();
    if (m_existing_children.size() <= relation)
        m_existing_children.resize(relation + 1);
    m_existing_children[relation].push_back(node);

    unsigned id = abs->get_id();
    if (m_actual_children.size() <= id)
        m_actual_children.resize(id + 1);
    m_actual_children[id] = node;
}

const modal_tree_node* modal_tree_node::last_child(unsigned int relation) const {
    SASSERT(m_existing_children.size() >= relation);
    SASSERT(!m_existing_children[relation].empty());
    return m_existing_children[relation].back();
}

modal_tree_node* modal_tree_node::get_created_child(syntax_tree_node* abs) {
    unsigned id = abs->get_id();
    if (id >= m_actual_children.size())
        return nullptr;
    return m_actual_children[id];
}

void modal_tree_node::remove_and_delete_last_child(unsigned int relation) {
    SASSERT(m_existing_children.size() >= relation);
    SASSERT(!m_existing_children[relation].empty());
    // delete m_existing_children[relation].back();
    m_existing_children[relation].pop_back();
}

void modal_tree_node::remove_last_spread(unsigned int relation) {
    SASSERT(m_spread.size() >= relation);
    SASSERT(!m_spread[relation].empty());
    m_spread[relation].pop_back();
}

bool modal_tree_node::is_blocked() {
    modal_tree_node* parent = this;
    while ((parent = parent->get_parent()) != nullptr) {
        // subset
        for (unsigned v : m_assignment_list) {
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
       << "Aux: " << w.aux_predicate() << "\n"
       << "Parent: " << (w.get_parent() == nullptr ? "null" : w.get_parent()->world_constant().to_string()) << "\n";
    if (w.get_syntax_node()) {
        os << "Abstract: a" << w.get_syntax_node()->get_id() << "\n"
           << "Template: " << w.get_syntax_node()->get_template(false) << "\n";
    }
    os << "\nReachable: \n";
    for (unsigned r = 0; r < w.get_child_relations_cnt(); r++) {
        for (const auto& reachable : w.get_children(r)) {
            os << "via r" << r << ": " << reachable->world_constant() << " [" << reachable->aux_predicate() << "]\n";
        }
    }
    os << "\nSpread: \n";
    for (unsigned r = 0; r < w.get_spread_relation_cnt(); r++) {
        for (const auto& spread : w.get_spread(r)) {
            os << "via r" << r << ": a" << spread.m_template->get_id() << " [" << spread.m_justification << "] Templ.: "
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

modal_tree_node* modal_tree::get_or_create_node(syntax_tree_node* abs, modal_tree_node* parent, const z3::expr& aux_predicate, z3::expr world_constant) {
    modal_tree_node* node;
    if (parent && (node = parent->get_created_child(abs))) {
        LOG("Recreated: " << node->world_constant() << " with aux " << node->m_aux_predicate);
    }
    else {
        bool named = (z3::ast)world_constant;
        if (!named)
            world_constant = z3::expr(m_ctx, Z3_mk_fresh_const(m_ctx, "world", get_world_sort()));
        node = new modal_tree_node(actual_size(), named, abs, parent, world_constant, aux_predicate);
        LOG("Creating: " << node->world_constant() << " with aux " << node->m_aux_predicate);
        m_expr_to_node[world_constant] = node;
        m_actual_nodes.push_back(node);
    }
    if (parent)
        parent->add_child(node, abs);
    m_existing_nodes.push_back(node);
    return node;
}

void modal_tree::remove_last_child(unsigned int relation) {
    // We delete the world from the model but keep the data-structure
    SASSERT(m_existing_nodes.size() > 1);
    //m_expr_to_node.erase(m_nodes.back()->world_constant());
    m_existing_nodes.back()->get_parent()->remove_and_delete_last_child(relation);
    m_existing_nodes.pop_back();
}

std::ostream& operator<<(std::ostream& os, const modal_tree& m) {
    for (const auto& w : m.get_existing_worlds()) {
        os << *w << "\n";
    }
    return os;
}
