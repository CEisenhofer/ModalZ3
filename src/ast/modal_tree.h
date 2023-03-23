#pragma once

#include "syntax_tree.h"

class modal_tree_node {
    
    friend class modal_tree;
    
    syntax_tree_node* m_abstract;
    modal_tree_node* m_parent;
    std::vector<modal_tree_node*> m_children;
    z3::expr m_world_constant;
    z3::expr m_aux_predicate;
    std::vector<bool> m_propagated; // ids of those abstract worlds that propagated already to this world
    std::vector<bool> m_assignments;
    
public:
    
    info* m_info = nullptr;
    
    modal_tree_node(syntax_tree_node* abs, modal_tree_node* parent, const z3::expr& world_constant, const z3::expr& aux_predicate) : m_abstract(abs), m_parent(parent), m_world_constant(world_constant), m_aux_predicate(aux_predicate) {}
    
    virtual ~modal_tree_node() {
        delete m_info;
    }
    
    syntax_tree_node* get_syntax_node() const {
        return m_abstract;
    }
    
    z3::expr world_constant() const {
        return m_world_constant;
    }
    
    z3::expr aux_predicate() const {
        SASSERT(m_aux_predicate.num_args() == 1 && eq(m_aux_predicate.arg(0), world_constant())); // for now; remove e.g., if the aux is a prop variable
        return m_aux_predicate;
    }

    bool is_assigned(unsigned variable) {
        return m_assignments.size() > variable && m_assignments[variable] != Z3_L_UNDEF;
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
    
    void add_child(modal_tree_node* node) {
        m_children.push_back(node);
    }

    void remove_and_delete_last_child() {
        SASSERT(!m_children.empty());
        delete m_children.back();
        m_children.pop_back();
    }
    
    bool is_root() const {
        return m_parent == nullptr;
    }
    
    modal_tree_node* get_parent() const {
        return m_parent;
    }
    
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
  
    std::vector<modal_tree_node*>::iterator begin() {
        return m_children.begin();
    }
    
    std::vector<modal_tree_node*>::iterator end() {
        return m_children.end();
    }
    
};

class modal_tree {
    
    z3::context& m_ctx;
    
    syntax_tree* m_syntax;
    modal_tree_node* m_root;
    
    std::vector<modal_tree_node*> m_nodes;
    std::unordered_map<z3::expr, modal_tree_node*, expr_hash, expr_eq> m_expr_to_node;
    
public:
    
    modal_tree(syntax_tree* syn, z3::expr init_world) : m_ctx(syn->ctx()), m_syntax(syn), m_root(create_node(syn->get_root(), nullptr, m_ctx.bool_val(true), init_world)) { }
    
    modal_tree_node* get_root() const {
        return m_root;
    }
    
    modal_tree_node* create_node(syntax_tree_node* abs, modal_tree_node* parent, const z3::expr& world_constant, const z3::expr& aux_predicate) {
        modal_tree_node* node = new modal_tree_node(abs, parent, world_constant, aux_predicate);
        SASSERT((parent == nullptr && abs->get_parent() == nullptr) || (parent->m_abstract->get_id() == abs->get_id()));
        parent->add_child(node);
        m_nodes.push_back(node);
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
    
};
