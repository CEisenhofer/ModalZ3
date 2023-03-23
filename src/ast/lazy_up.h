#pragma once
#include "modal_to_euf_base.h"

class lazy_up;

class undo_trail {
public:
    virtual void undo() = 0;
};

class assignment_undo : public undo_trail {
    modal_tree_node* m_world;
    unsigned m_var;
public:
    assignment_undo(modal_tree_node* world, unsigned var) : m_world(world), m_var(var) {}
    void undo() override;
};

class create_world_undo : public undo_trail {
    modal_tree_node* m_parent_world;
public:
    create_world_undo(modal_tree_node* parent) : m_parent_world(parent) {}
    void undo() override;
};

class lazy_up : public user_propagator_base, modal_to_euf_base {

    friend class assignment_undo;

    std::stack<unsigned> m_trail_sz;
    std::stack<undo_trail*> m_trail;
    std::unordered_map<std::string, unsigned> m_str_to_var;

public:

    void push() override {
        m_trail_sz.push(m_trail.size());
    }

    void pop(unsigned num_scopes) override {
        for (int i = 0; i < num_scopes; i++) {
            undo_trail* trail = m_trail.top();
            m_trail.pop();
            trail->undo();
            delete trail;
        }
    }

    unsigned get_variable(const func_decl& decl);

    void fixed(const expr& e, const expr& value) override;

    ~lazy_up() {
        while (!m_trail.empty()) {
            undo_trail* trail = m_trail.top();
            m_trail.pop();
            delete trail;
        }
    }
};
