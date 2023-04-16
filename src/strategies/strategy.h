#pragma once

#include <chrono>
#include <optional>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <z3++.h>

#include "expr_info.h"
#include "modal_tree.h"

using namespace z3;

struct modal_decls {

    friend class lazy_up;

    sort world_sort, relation_sort;
    func_decl dia, box;
    func_decl global;
    func_decl reachable;
    func_decl placeholder;
    
private:
    func_decl reachable_uf; // user-function
    
public:
    
    modal_decls(const sort& world_sort, const sort& relation_sort) :
        world_sort(world_sort), relation_sort(relation_sort),
        dia(world_sort.ctx()), box(world_sort.ctx()),
        global(world_sort.ctx()),
        reachable(world_sort.ctx()),
        placeholder(world_sort.ctx()),
        reachable_uf(world_sort.ctx()) {}
        
    z3::sort_vector get_sorts();
    z3::func_decl_vector get_decls();
    static modal_decls create_default(z3::context& ctx);
};

class strategy {
protected:
    
    context& m_ctx;
    solver m_solver;
    syntax_tree* m_syntax_tree = nullptr;
    modal_tree* m_modal_tree = nullptr;

    std::stack<std::vector<expr>> m_processed_args;
    std::stack<expr_info> m_apply_list;

    check_result m_last_result;

    modal_decls m_decls;

    func_decl_vector m_uf_list;
    std::unordered_set<func_decl, func_decl_hash, func_decl_eq> m_uf_set;
    std::unordered_map<func_decl, unsigned, func_decl_hash, func_decl_eq> m_uf_to_id;
    
    std::unordered_map<func_decl, std::optional<func_decl>, func_decl_hash, func_decl_eq> m_orig_uf_to_new_uf;

    std::unordered_map<func_decl, unsigned, func_decl_hash, func_decl_eq> m_relation_to_id;
    func_decl_vector m_relation_list;

    bool m_is_solving = false;
    
    bool m_is_benchmark = false;
    std::chrono::microseconds m_solving_time;

    bool is_world(const sort& s) const;
    bool is_relation(const sort& s) const;
    bool is_modal(const func_decl& decl) const;
    bool is_box(const func_decl& decl) const;
    bool is_dia(const func_decl& decl) const;
    bool is_placeholder(const func_decl& decl) const;
    bool is_global(const func_decl& decl) const;
    bool is_reachable_extern(const func_decl& decl) const;
    bool is_ml_interpreted(const func_decl& decl) const;
    
    strategy(context& ctx, const modal_decls& decls);
    
    virtual bool is_blast_eq() const { return false; }
    virtual bool is_nnf() const { return false; } // TODO: Implement in simplify
    virtual bool is_incremental_parsing() const { return false; }
    virtual bool is_widen_modals() const { return true; } // (dia F1 || dia F2) ==> dia (F1 || F2)
    // might increase performance of MBQI!

    expr simplify_formula(const expr& e);
    virtual expr create_formula(const expr& e) = 0;

    virtual void output_model(const model& model, std::ostream &ostream) = 0;
    
    z3::expr post_rewrite(const func_decl& f, expr_vector& args);
    bool pre_rewrite(std::stack<expr_info>& expr_to_process, expr_info& current);

    virtual check_result solve(const z3::expr& e)  { 
        m_solver.add(e); 
        return m_solver.check();
    }

public:
    
    strategy() = delete;
    strategy(const strategy& ctx) = delete;
    
    virtual ~strategy() {
        delete m_syntax_tree;
        delete m_modal_tree;
    }
    
    void set_is_benchmark(bool is_benchmark) {
        m_is_benchmark = is_benchmark;
    }
    
    std::chrono::microseconds solving_time() const {
        return m_solving_time;
    }

    void set_timeout(unsigned limit) {
        m_solver.set(":timeout", limit);
    }

    void set_memout(unsigned limit) {
        m_solver.set(":max_memory", limit);
    }

    const z3::sort& get_world_sort() const {
        return m_decls.world_sort;
    }

    z3::expr fresh_world_constant() const {
        return { m_ctx, Z3_mk_fresh_const(m_ctx, "world", m_decls.world_sort) };
    }


    context& ctx() { return m_ctx; }
    
    expr simplify(const expr& e);
    
    check_result check(expr e);
    
    void output_state(std::ostream& ostream);
    
    // Probably inefficient. However, we want a solver and not a model-checker. Propositional only for now
    virtual Z3_lbool model_check(const z3::expr& e) { throw exception("Not implemented!"); }

    virtual unsigned domain_size() = 0;
};
