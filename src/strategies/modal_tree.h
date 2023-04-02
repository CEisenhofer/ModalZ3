#pragma once

#include "syntax_tree.h"

struct spread_info {
    syntax_tree_node* m_template;
    expr m_justification;

    spread_info(syntax_tree_node* temp, const expr& justification) : m_template(temp), m_justification(justification) {}
};

class modal_tree_node {
    
    friend class modal_tree;

    const unsigned m_id;
    
    syntax_tree_node* m_abstract;
    modal_tree_node* m_parent;
    std::vector<std::vector<modal_tree_node*>> m_children; // negative modal operators
    std::vector<std::vector<spread_info>> m_spread; // positive modal operators
    z3::expr m_world_constant;
    z3::expr m_aux_predicate;
    // std::vector<bool> m_propagated; // ids of those abstract worlds that propagated already to this world
    std::vector<Z3_lbool> m_assignments;

public:
    
    modal_tree_node(unsigned id, syntax_tree_node* abs, modal_tree_node* parent, const z3::expr& world_constant, const z3::expr& aux_predicate) : m_id(id), m_abstract(abs), m_parent(parent), m_world_constant(world_constant), m_aux_predicate(aux_predicate) {}
    
    virtual ~modal_tree_node() { }

    unsigned get_id() const {
        return m_id;
    }
    
    syntax_tree_node* get_syntax_node() const {
        return m_abstract;
    }
    
    z3::expr world_constant() const {
        return m_world_constant;
    }
    
    z3::expr aux_predicate() const {
        SASSERT(m_aux_predicate.num_args() == 1 && eq(m_aux_predicate.arg(0), m_parent->world_constant()));
        return m_aux_predicate;
    }

    bool is_assigned(unsigned variable) {
        return m_assignments.size() > variable && m_assignments[variable] != Z3_L_UNDEF;
    }

    Z3_lbool get_assignment(unsigned variable) {
        if (m_assignments.size() <= variable)
            return Z3_L_UNDEF;
        return m_assignments[variable];
    }

    void unassign(unsigned variable) {
        SASSERT(is_assigned(variable));
        assign(variable, Z3_L_UNDEF);
    }

    void assign(unsigned variable, bool val) {
        assign(variable, val ? Z3_L_TRUE : Z3_L_FALSE);
    }

    void assign(unsigned variable, Z3_lbool val) {
        if (m_assignments.size() <= variable) {
            m_assignments.resize(variable + 1);
        }
        m_assignments[variable] = val;
    }

    bool is_root() const {
        return m_parent == nullptr;
    }
    
    modal_tree_node* get_parent() const {
        return m_parent;
    }

    void add_spread(const spread_info& info, unsigned relation) {
        if (m_spread.size() <= relation)
            m_spread.resize(relation + 1);
        m_spread[relation].push_back(info);
    }

    const spread_info& last_spread(unsigned relation) const {
        SASSERT(m_spread.size() >= relation);
        SASSERT(!m_spread[relation].empty());
        return m_spread[relation].back();
    }

    unsigned get_spread_relation_cnt() const {
        return m_spread.size();
    }

    const std::vector<spread_info>& get_spread(unsigned relation) {
        SASSERT(relation < m_children.size());
        return m_spread[relation];
    }

#if 0
    bool has_propagated_by(syntax_tree_node* n) const {
        if (m_propagated.size() <= n->get_id())
            return false;
        return m_propagated[n->get_id()];
    }

    void set_propagated_by(syntax_tree_node* n, bool val) {
        for (unsigned i = m_propagated.size(); i <= n->get_id(); i++)
            m_propagated.push_back(false);

        m_propagated[n->get_id()] = val;
    }
#endif

    void add_child(modal_tree_node* node, unsigned relation) {
        if (m_children.size() <= relation)
            m_children.resize(relation + 1);
        m_children[relation].push_back(node);
    }

    const modal_tree_node* last_child(unsigned relation) const {
        SASSERT(m_children.size() >= relation);
        SASSERT(!m_children[relation].empty());
        return m_children[relation].back();
    }

    unsigned get_child_relations_cnt() const {
        return m_children.size();
    }

    const std::vector<modal_tree_node*> get_children(unsigned relation) const {
        SASSERT(relation < m_children.size());
        return m_children[relation];
    }

    void remove_and_delete_last_child(unsigned relation) {
        SASSERT(m_children.size() >= relation);
        SASSERT(!m_children[relation].empty());
        delete m_children[relation].back();
        m_children[relation].pop_back();
    }

    void remove_last_spread(unsigned relation) {
        SASSERT(m_spread.size() >= relation);
        SASSERT(!m_spread[relation].empty());
        m_spread[relation].pop_back();
    }
};

class modal_tree {
    
    z3::context& m_ctx;

    syntax_tree* m_syntax;

    std::vector<modal_tree_node*> m_nodes;
    std::unordered_map<z3::expr, modal_tree_node*, expr_hash, expr_eq> m_expr_to_node;
    
public:
    
    modal_tree(syntax_tree* syn) : m_ctx(syn->ctx()), m_syntax(syn) {
        create_node(syn->get_root(), nullptr, -1, m_ctx.bool_val(true));
    }
    
    modal_tree_node* get_root() const {
        SASSERT(!m_nodes.empty());
        SASSERT(m_nodes[0]->is_root());
        return m_nodes[0];
    }

    sort get_world_sort() const {
        return m_syntax->get_world_sort();
    }
    
    modal_tree_node* create_node(syntax_tree_node* abs, modal_tree_node* parent, unsigned relation, const z3::expr& aux_predicate) {
        z3::expr new_world = z3::expr(m_ctx, Z3_mk_fresh_const(m_ctx, "world", get_world_sort()));
        modal_tree_node* node = new modal_tree_node(m_nodes.size(), abs, parent, new_world, aux_predicate);
        LOG("Creating: w" << node->get_id() << " internally " << node->world_constant() << " because of " << !node->m_aux_predicate);
        if (parent)
            parent->add_child(node, relation);
        m_nodes.push_back(node);
        m_expr_to_node[new_world] = node;
        return node;
    }
    
    ~modal_tree() {
        for (unsigned i = 0; i < m_nodes.size(); i++)
            delete m_nodes[i];
    }
    
    unsigned size() const {
        return m_nodes.size();
    }

    modal_tree_node* get(const z3::expr& e) const {
        auto iterator = m_expr_to_node.find(e);
        SASSERT(iterator != m_expr_to_node.end());
        return iterator->second;
    }

    const std::vector<modal_tree_node*>& get_worlds() const {
        return m_nodes;
    };

    void remove_last_child(unsigned relation) {
        // TODO: Or better keep the entry and just disable it?
        SASSERT(m_nodes.size() > 1);
        m_expr_to_node.erase(m_nodes.back()->world_constant());
        m_nodes.back()->get_parent()->remove_and_delete_last_child(relation);
        m_nodes.pop_back();
    }
    
};
