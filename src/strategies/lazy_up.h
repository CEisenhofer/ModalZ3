#pragma once
#include <utility>

#include "strategy.h"

class lazy_up;

class undo_trail {
public:
    virtual ~undo_trail() = default;
    virtual void undo() = 0;
    virtual void output(std::ostream& os) = 0;
};

std::ostream& operator<<(std::ostream& os, undo_trail* undo);

class assignment_undo : public undo_trail {
    modal_tree_node* m_world;
    unsigned m_var;
public:
    assignment_undo(modal_tree_node* world, unsigned var) : m_world(world), m_var(var) {}
    void undo() override;
    void output(std::ostream& os) override {
        os << "assigned v" << m_var << " to " << (m_world->get_assignment(m_var) == Z3_L_TRUE ? "true" : "false");
    }
};

class lazy_up;

class graph_update : public undo_trail {
    
protected:
    
    lazy_up* m_up;
    
    graph_update(lazy_up* up) : m_up(up) {}
    
public:

    virtual bool apply() = 0;
    virtual bool operator==(graph_update* op) const = 0;
};

class new_spread_update : public graph_update {
    
    syntax_tree_node* m_template;
    modal_tree_node* m_parent;
    expr m_justification;
    
public:
    
    new_spread_update(lazy_up* up, syntax_tree_node* temp, modal_tree_node* parent, expr just) : graph_update(up), m_template(temp), m_parent(parent), m_justification(std::move(just)) { }
    
    bool apply() override;
    void undo() override;
    
    bool operator==(graph_update* op) const { // For Debug
        return op && (m_template == ((new_spread_update*)op)->m_template) && (m_parent == ((new_spread_update*)op)->m_parent) && z3::eq(m_justification, (((new_spread_update*)op)->m_justification));
    }
    void output(std::ostream& os) override;
};

class new_world_update : public graph_update {
    
    syntax_tree_node* m_template;
    modal_tree_node* m_parent;
    modal_tree_node* m_created = nullptr;
    expr m_justification;
    
public:
    
    new_world_update(lazy_up* up, syntax_tree_node* temp, modal_tree_node* parent, expr just) : graph_update(up), m_template(temp), m_parent(parent), m_justification(std::move(just)) { }
    
    bool apply() override;
    void undo() override;
    
    void output(std::ostream& os) override;
    bool operator==(graph_update* op) const {
        return op && (m_template == ((new_world_update*)op)->m_template) && (m_parent == ((new_world_update*)op)->m_parent) && z3::eq(m_justification, (((new_world_update*)op)->m_justification));
    }
};

class connect_worlds_update :  public graph_update {
    
    connection_info m_connection;
    unsigned m_relation;
    
public:
    
    connect_worlds_update(lazy_up* up, modal_tree_node* w1, modal_tree_node* w2, unsigned relation, expr just) : graph_update(up), m_connection(w1, w2, std::move(just)), m_relation(relation) { 
        SASSERT(w1->is_named());
        SASSERT(w2->is_named());
    }
    
    bool apply() override;
    void undo() override;
    
    void output(std::ostream& os) override;
    bool operator==(graph_update* op) const {
        return op && (m_relation == ((connect_worlds_update*)op)->m_relation) && m_connection == ((connect_worlds_update*)op)->m_connection;
    }
};

class added_graph_update_undo : public undo_trail {
    std::vector<graph_update*>& m_pending_updates; // delay world generation to final
    graph_update* m_added;
public:
    added_graph_update_undo(std::vector<graph_update*>& to_init, graph_update* to_remove) : m_pending_updates(to_init), m_added(to_remove) {}
    void undo() override;
    void output(std::ostream& os) override {
        os << "added: " << m_added;
    }
};

class removed_graph_update_undo : public undo_trail {
    std::vector<graph_update*>& m_pending_updates;
    graph_update* m_removed;
public:
    removed_graph_update_undo(std::vector<graph_update*>& to_init, graph_update* info) : m_pending_updates(to_init), m_removed(info) {}
    void undo() override;
    void output(std::ostream& os) override {
        os << "removed: " << m_removed; 
    }
};

void log_clause(z3::expr const& proof, z3::expr_vector const& clause);

class lazy_up : public strategy, user_propagator_base {

    friend class assignment_undo;
    friend class new_spread_update;
    friend class new_world_update;
    friend class connect_worlds_update;
    
    using user_propagator_base::ctx;

    std::vector<unsigned> m_trail_sz;
    std::stack<undo_trail*> m_trail;
    
    // delay world generation to final; order has to be irrelevant (reverting blocking will add back non-chronologically)
    std::vector<graph_update*> m_pending_updates;
    
    z3::expr_vector m_assertions;
    
    std::vector<syntax_tree_node*> m_global; // true \sqsubseteq F

#ifndef NDEBUG
    on_clause_eh_t log = log_clause;
    const on_clause logger;
#endif


    bool is_reachable_intern(const func_decl &decl) const {
        return z3::eq(decl, m_decls.reachable_uf);
    }
    
    void add_trail(undo_trail* to_undo) {
        LOG("Adding: " << to_undo);
        m_trail.push(to_undo);
    }

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
    void propagate_to(const connection_info& connection, unsigned relation);
    void propagate_from(syntax_tree_node* temp, modal_tree_node* parent, unsigned relation, const expr& justification);

    void apply_unconstrained(modal_tree_node* world);
    
    unsigned get_or_add_relation(const expr& relation);
    
    unsigned get_variable(const func_decl& decl) const;
    unsigned get_or_create_variable(const func_decl& decl);

    void add_global(syntax_tree_node* rhs) {
        m_global.push_back(rhs);
    }

    void try_global_to_local();
    bool try_apply_local(syntax_tree_node* abs);
    
    void output_model(const model& model, std::ostream &ostream) override;
    
    virtual check_result solve(const z3::expr& e) { 
        m_solver.add(e); 
        check_result res = m_solver.check();
        if (res == z3::sat)
            m_modal_tree->remove_blocked();
        return res;
    }

public:

    explicit lazy_up(context& ctx, const modal_decls& decls) :
        strategy(ctx, decls), user_propagator_base(&m_solver),
        m_assertions(ctx)
#ifndef NDEBUG
        , logger(m_solver, log)
#endif
        {

        register_fixed();
        register_final();
        register_created();
#ifndef NDEBUG
        register_decide();
#endif
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
    void decide(expr& e, unsigned& bit, Z3_lbool& val) override;

    user_propagator_base* fresh(context& new_ctx) override {
        return this;
    }

    Z3_lbool model_check(const z3::expr& e) override;
    
    unsigned domain_size() override;
};
