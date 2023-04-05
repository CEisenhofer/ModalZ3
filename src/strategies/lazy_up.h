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
    syntax_tree_node* m_template;
    modal_tree_node* m_parent;
    std::optional<expr> m_justification;
    bool m_positive;

    init_info() = default;
    init_info(syntax_tree_node* temp, modal_tree_node* parent, expr just, bool positive) : m_template(temp), m_parent(parent), m_justification(just), m_positive(positive) {}
    
    const expr& just() const {
        return *m_justification;
    }
};

class added_init_info_undo : public undo_trail {
    std::vector<init_info>& m_to_init; // delay world generation to final
    init_info m_to_remove;
public:
    added_init_info_undo(std::vector<init_info>& to_init, const init_info& to_remove) : m_to_init(to_init), m_to_remove(to_remove) {}
    void undo() override;
};

class removed_init_info_undo : public undo_trail {
    std::vector<init_info>& m_to_init;
    init_info m_info;
public:
    removed_init_info_undo(std::vector<init_info>& to_init, init_info info) : m_to_init(to_init), m_info(info) {}
    void undo() override;
};


class lazy_up : public strategy, user_propagator_base {

    friend class assignment_undo;
    using user_propagator_base::ctx;

    std::vector<unsigned> m_trail_sz;
    std::stack<undo_trail*> m_trail;
    
    // delay world generation to final; order has to be irrelevant (reverting blocking will add back non-chronologically)
    std::vector<init_info> m_to_init;
    
    z3::expr_vector m_assertions;
    
    std::vector<syntax_tree_node*> m_unconstraint_global; // true \sqsubseteq F
    std::vector<std::vector<syntax_tree_node*>> m_constraint_global; // A \sqsubseteq F

    void propagate(const z3::expr_vector& jst, const z3::expr& conseq) {
        if (m_is_solving) {
            z3::user_propagator_base::propagate(jst, conseq);
            return;
        }
        if (jst.empty())
            m_assertions.push_back(conseq);
        else
            m_assertions.push_back(implies(mk_and(jst), conseq));
    }
    
    void propagate(const z3::expr& jst, const z3::expr& conseq) {
        z3::expr_vector vec(jst.ctx());
        if (!jst.is_true()) 
            vec.push_back(jst);
        return propagate(vec, conseq);
    }
    
    void propagate(const z3::expr& jst1, const z3::expr& jst2, const z3::expr& conseq) {
        if (jst1.is_true())
            return propagate(jst2, conseq);
        if (jst2.is_true())
            return propagate(jst1, conseq);
        z3::expr_vector vec(jst1.ctx()); 
        vec.push_back(jst1);
        vec.push_back(jst2);
        return propagate(vec, conseq);
    }
    
    void propagate_to(modal_tree_node* new_world, unsigned relation);
    void propagate_from(syntax_tree_node* temp, modal_tree_node* parent, unsigned relation, const expr& justification);

    void apply_unconstrained(modal_tree_node* world);
    
    unsigned get_variable(const func_decl& decl) const;
    unsigned get_or_create_variable(const func_decl& decl);

    void add_unconstraint(syntax_tree_node* rhs) {
        m_unconstraint_global.push_back(rhs);
    }

    void add_constraint(const func_decl& var, bool neg, syntax_tree_node* rhs);

    void output_model(const model& model, std::ostream &ostream) override;

public:

    explicit lazy_up(context& ctx, const modal_decls& decls) :
        strategy(ctx, decls), user_propagator_base(&m_solver),
        m_assertions(ctx) {

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

    Z3_lbool model_check(const z3::expr& e) override;
    
    unsigned domain_size() override;
};
