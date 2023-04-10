#pragma once

#include "syntax_tree.h"

struct spread_info {
    syntax_tree_node* m_template;
    z3::expr m_justification;

    spread_info(syntax_tree_node* temp, const z3::expr& justification) : m_template(temp), m_justification(justification) {}
};

class modal_tree_node {
    
    friend class modal_tree;

    const unsigned m_id;
    
    syntax_tree_node* m_abstract;
    modal_tree_node* m_parent;
    std::vector<std::vector<modal_tree_node*>> m_existing_children; // negative modal operators
    std::vector<std::vector<spread_info>> m_spread; // positive modal operators

    // contains also children that have been removed again by backtracking
    // => CDCL might assign even values, although they do not even exist any more (we have to retain them)
    std::vector<modal_tree_node*> m_actual_children; // indexed by abstract id

    z3::expr m_world_constant;
    z3::expr m_aux_predicate;
    std::vector<Z3_lbool> m_assignment_set;
    std::vector<unsigned> m_assignment_list;
    
    modal_tree_node* m_blocked_by = nullptr;

public:
    
    modal_tree_node(unsigned id, syntax_tree_node* abs, modal_tree_node* parent, const z3::expr& world_constant, const z3::expr& aux_predicate) : m_id(id), m_abstract(abs), m_parent(parent), m_world_constant(world_constant), m_aux_predicate(aux_predicate) {}
    
    virtual ~modal_tree_node() { }

    unsigned get_id() const {
        return m_id;
    }
    
    syntax_tree_node* get_syntax_node() const {
        return m_abstract;
    }
    
    modal_tree_node* blocked_by() const {
        return m_blocked_by;
    }
    
    z3::expr world_constant() const {
        return m_world_constant;
    }
    
    z3::expr aux_predicate() const {
        SASSERT(m_aux_predicate.is_true() || (m_aux_predicate.num_args() == 1 && eq(m_aux_predicate.arg(0), m_parent->world_constant())));
        return m_aux_predicate;
    }

    bool is_assigned(unsigned variable) const;

    Z3_lbool get_assignment(unsigned variable) const;

    unsigned get_assignment_cnt() const {
        return m_assignment_set.size();
    }

    void unassign(unsigned variable);

    void assign(unsigned variable, bool val);

    void assign(unsigned variable, Z3_lbool val);

    bool is_root() const {
        return m_parent == nullptr;
    }
    
    modal_tree_node* get_parent() const {
        return m_parent;
    }

    void add_spread(const spread_info& info, unsigned relation);

    const spread_info& last_spread(unsigned relation) const;

    unsigned get_spread_relation_cnt() const {
        return m_spread.size();
    }

    const std::vector<spread_info>& get_spread(unsigned relation) const {
        SASSERT(relation < m_spread.size());
        return m_spread[relation];
    }

    void add_child(modal_tree_node* node, syntax_tree_node* abs);

    const modal_tree_node* last_child(unsigned relation) const;

    unsigned get_child_relations_cnt() const {
        return m_existing_children.size();
    }

    modal_tree_node* get_created_child(syntax_tree_node* abs);

    const std::vector<modal_tree_node*>& get_children(unsigned relation) const {
        SASSERT(relation < m_existing_children.size());
        return m_existing_children[relation];
    }

    void remove_and_delete_last_child(unsigned relation);

    void remove_last_spread(unsigned relation);
    
    bool is_blocked();
};

std::ostream& operator<<(std::ostream& os, const modal_tree_node& w);

class modal_tree {
    
    z3::context& m_ctx;

    syntax_tree* m_syntax;

    std::vector<modal_tree_node*> m_existing_nodes;
    std::vector<modal_tree_node*> m_actual_nodes; // superset of existing worlds (those in the model)
    std::unordered_map<z3::expr, modal_tree_node*, expr_hash, expr_eq> m_expr_to_node;
    
public:
    
    modal_tree(syntax_tree* syn) : m_ctx(syn->ctx()), m_syntax(syn) {
        get_or_create_node(syn->get_root(), nullptr, m_ctx.bool_val(true));
    }
    
    modal_tree_node* get_root() const {
        SASSERT(!m_existing_nodes.empty());
        SASSERT(m_existing_nodes[0]->is_root());
        return m_existing_nodes[0];
    }

    z3::sort get_world_sort() const {
        return m_syntax->get_world_sort();
    }
    
    modal_tree_node* get_or_create_node(syntax_tree_node* abs, modal_tree_node* parent, const z3::expr& aux_predicate);
    
    ~modal_tree() {
        for (unsigned i = 0; i < m_actual_nodes.size(); i++)
            delete m_actual_nodes[i];
    }
    
    unsigned existing_size() const {
        return m_existing_nodes.size();
    }

    unsigned actual_size() const {
        return m_actual_nodes.size();
    }

    modal_tree_node* get(const z3::expr& e) const {
        auto iterator = m_expr_to_node.find(e);
        SASSERT(iterator != m_expr_to_node.end());
        return iterator->second;
    }

    const std::vector<modal_tree_node*>& get_existing_worlds() const {
        return m_existing_nodes;
    };

    void remove_last_child(unsigned relation);
    
};

std::ostream& operator<<(std::ostream& os, const modal_tree& m);
