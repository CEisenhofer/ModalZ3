#pragma once

#include <vector>
#include <stack>
#include <z3++.h>

#include "assertion.h"
    
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

struct info {
    
    virtual ~info() {}
    
};

class syntax_tree_node {
    
    friend class syntax_tree;
    
    unsigned m_id;
    syntax_tree_node* m_parent = nullptr;
    std::vector<syntax_tree_node*> m_children;
    
    z3::expr m_expr; // something used to create instances
    
    std::unordered_map<z3::expr, syntax_tree_node*, expr_hash, expr_eq> m_expr_to_child; // not necessarily equal to m_ast [can be rewritten]. The map contains the original expressions
    
    syntax_tree_node(unsigned id, z3::context& c) : m_id(id), m_expr(c) { }
    
public:
    
    info* m_info = nullptr;
    
    virtual ~syntax_tree_node() {
        delete m_info;
    }
    
    syntax_tree_node* get_child(const z3::expr& e) const {
        auto it = m_expr_to_child.find(e);
        if (it == m_expr_to_child.end())
            return nullptr;
        return it->second;
    }
    
    unsigned get_id() const {
        return m_id;
    }
    
    void set_parent(syntax_tree_node* node) {
        m_parent = node;
    }
    
    const syntax_tree_node* get_parent() const {
        return m_parent;
    }
    
    void set_expr(const z3::expr& e) {
        m_expr = e;
    }
    
    const z3::expr& get_template() const {
        return m_expr;
    }
    
    void add_child(syntax_tree_node* node) {
        m_children.push_back(node);
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
    
    unsigned get_depth() const {
        unsigned depth = 0;
        const syntax_tree_node* prev = this;
        for (; prev->is_root(); depth++) {}
        return depth;
    }
    
};

class syntax_tree {
    
    z3::context& m_ctx;
    
    unsigned m_size;
    std::vector<syntax_tree_node*> m_nodes;
    syntax_tree_node* const m_root;
    
    
public:
    
    syntax_tree(z3::context& c) : m_ctx(c), m_size(0), m_root(create_node()) { }
    
    syntax_tree_node* get_root() const {
        return m_root;
    }
    
    syntax_tree_node* create_node() {
        syntax_tree_node* node = new syntax_tree_node(m_size++, m_ctx);
        m_nodes.push_back(node);
        return node;
    }
    
    z3::context& ctx() {
        return m_ctx;
    }
    
    ~syntax_tree() {
        for (auto& n : m_nodes)
            delete n;
    }
    
};