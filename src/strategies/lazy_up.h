#pragma once
#include "strategy.h"

class lazy_up;

class undo_trail {
public:
    virtual ~undo_trail() = default;
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
    modal_tree* m_modal_tree;
    unsigned m_relation;
public:
    create_world_undo(modal_tree* modal_tree, unsigned relation) : m_modal_tree(modal_tree), m_relation(relation) {}
    void undo() override;
};

class add_spread_info_undo : public undo_trail {
    modal_tree_node* m_world;
    unsigned m_relation;
public:
    add_spread_info_undo(modal_tree_node* world, unsigned relation) : m_world(world), m_relation(relation) {}
    void undo() override;
};

struct init_info {
    syntax_tree_node* const m_template;
    modal_tree_node* const m_parent;
    expr const m_justification;
    bool const m_positive;

    init_info(syntax_tree_node* temp, modal_tree_node* parent, expr just, bool positive) : m_template(temp), m_parent(parent), m_justification(just), m_positive(positive) {}
};

class added_init_info_undo : public undo_trail {
    std::stack<init_info>& m_to_init; // delay world generation to final
public:
    added_init_info_undo(std::stack<init_info>& to_init) : m_to_init(to_init) {}
    void undo() override;
};

class removed_init_info_undo : public undo_trail {
    std::stack<init_info>& m_to_init;
    init_info m_info;
public:
    removed_init_info_undo(std::stack<init_info>& to_init, init_info info) : m_to_init(to_init), m_info(info) {}
    void undo() override;
};


class lazy_up : public strategy, user_propagator_base {

    friend class assignment_undo;
    using user_propagator_base::ctx;

    std::stack<unsigned> m_trail_sz;
    std::stack<undo_trail*> m_trail;
    std::stack<init_info> m_to_init; // delay world generation to final

    void propagate_to(modal_tree_node* new_world, unsigned relation);
    void propagate_from(syntax_tree_node* temp, modal_tree_node* parent, unsigned relation, const expr& justification);

    unsigned get_variable(const func_decl& decl);

public:

    explicit lazy_up(context& ctx, const sort& world_sort, const sort& reachability_sort, const func_decl& dia, const func_decl& box, const expr& placeholder) :
        strategy(ctx, world_sort, reachability_sort, dia, box, placeholder), user_propagator_base(&m_solver) {

        register_fixed();
        register_final();
        register_created();
    }

    ~lazy_up() {
        while (!m_trail.empty()) {
            undo_trail* trail = m_trail.top();
            m_trail.pop();
            delete trail;
        }
    }

    expr create_formula(const expr& e) override;

    void push() override;
    void pop(unsigned num_scopes) override;
    void fixed(const expr& e, const expr& value) override;
    void final() override;
    void created(const expr& e) override;

    user_propagator_base* fresh(context& new_ctx) override {
        return this;
    }

    void output_model(const model& model, std::ostream &ostream) override;
};
