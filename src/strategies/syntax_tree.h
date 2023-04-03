#pragma once

#include <stack>
#include <vector>
#include <z3++.h>

#include "assertion.h"
#include "logging.h"
    
struct expr_hash {
    size_t operator()(const z3::expr& e) const {
        return e.hash();
    }
};
struct expr_eq {
    bool operator()(const z3::expr& e1, const z3::expr& e2) const {
        return eq(e1, e2);
    }
};

struct func_decl_hash {
    size_t operator()(const z3::func_decl& f) const {
        return f.hash();
    }
};
struct func_decl_eq {
    bool operator()(const z3::func_decl& f1, const z3::func_decl& f2) const {
        return eq(f1, f2);
    }
};

class syntax_tree_node {
    
    friend class syntax_tree;
    
    unsigned m_id;
    syntax_tree_node* const m_parent;
    std::vector<syntax_tree_node*> m_children;
    
    const unsigned m_relation;

    z3::expr m_template; // something used to create instances
    const z3::expr m_aux; // the expression that triggers this node

    std::unordered_map<z3::expr, syntax_tree_node*, expr_hash, expr_eq> m_expr_to_repr; // not necessarily equal to m_template [can be rewritten]. The map contains the original expressions
    
    syntax_tree_node(unsigned id, syntax_tree_node* parent, unsigned relation, const z3::expr& aux) : m_id(id), m_parent(parent), m_relation(relation), m_template(aux.ctx()), m_aux(aux) {}
    
public:
    
    syntax_tree_node* get_child(const z3::expr& e) const;

    unsigned get_id() const {
        return m_id;
    }

    const syntax_tree_node* get_parent() const {
        return m_parent;
    }

    void set_template(const z3::expr& temp) {
        m_template = temp;
    }

    z3::expr get_template(bool pos) const;

    bool is_template_false() const {
        return m_template.is_false();
    }

    z3::expr get_aux() const {
        return m_aux;
    }

    bool is_root() const {
        return m_parent == nullptr;
    }
  
    std::vector<syntax_tree_node*>::iterator begin() {
        return m_children.begin();
    }
    
    std::vector<syntax_tree_node*>::iterator end() {
        return m_children.end();
    }
    
    unsigned get_relation() const {
        return m_relation;
    }

    z3::expr initialize(const z3::expr& world, bool positive) const;

    std::string to_string() const;
    std::string aux_to_string() const;
};

class strategy;

class syntax_tree {
    
    std::vector<syntax_tree_node*> m_nodes;
    strategy* const m_base;
    syntax_tree_node* const m_root;
    std::unordered_map<z3::func_decl, syntax_tree_node*, func_decl_hash, func_decl_eq> m_func_to_abs;

public:
    
    syntax_tree(strategy* base);
    
    syntax_tree_node* get_root() const;

    const z3::sort& get_world_sort() const;

    syntax_tree_node* create_node(syntax_tree_node* parent, unsigned relation, const z3::expr& orig_subformula);
    syntax_tree_node* create_node(const z3::expr& orig_subformula) {
        return create_node(nullptr, -1, orig_subformula);
    }

    syntax_tree_node* get_node(const z3::func_decl& f);

    z3::context& ctx();
    
    ~syntax_tree() {
        for (auto& n : m_nodes)
            delete n;
    }
    
};
