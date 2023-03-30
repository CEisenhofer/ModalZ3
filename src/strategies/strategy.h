#pragma once

#include <optional>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <z3++.h>

#include "expr_info.h"
#include "modal_tree.h"

using namespace z3;

class strategy {
protected:
    
    context& m_ctx;
    solver m_solver;
    syntax_tree* m_syntax_tree = nullptr;
    modal_tree* m_modal_tree = nullptr;

    std::stack<std::vector<expr>> m_processed_args;
    std::stack<expr_info> m_apply_list;

    check_result m_last_result;

    const sort m_world_sort;
    const sort m_reachability_sort;
    const func_decl m_box_decl;
    const func_decl m_dia_decl;
    const func_decl m_reachable_decl;
    const expr m_placeholder;

    func_decl_vector m_uf_list;
    std::unordered_set<func_decl, func_decl_hash, func_decl_eq> m_uf_set;
    std::unordered_map<func_decl, unsigned, func_decl_hash, func_decl_eq> m_uf_to_id;

    std::unordered_map<func_decl, unsigned, func_decl_hash, func_decl_eq> m_relation_to_id;
    func_decl_vector m_relation_list;

    bool is_modal(const func_decl& decl) const;
    
    explicit strategy(context& ctx, const sort& world_sort, const sort& reachability_sort, const func_decl& dia, const func_decl& box, const func_decl& reachable, const expr& placeholder);
    
    virtual bool is_blast_eq() const { return false; }
    virtual bool is_nnf() const { return false; } // TODO: Implement in simplify
    virtual bool is_incremental_parsing() const { return false; }

    expr simplify_formula(const expr& e);
    virtual expr create_formula(const expr& e) = 0;

    virtual void output_model(const model& model, std::ostream &ostream) = 0;
    
    bool post_rewrite(expr_info& current, expr_vector& args);
    bool pre_rewrite(std::stack<expr_info>& expr_to_process, expr_info& current);

    virtual check_result solve(const z3::expr& e) { m_solver.add(e); return m_solver.check(); }

public:
    
    strategy() = delete;
    strategy(const strategy& ctx) = delete;
    
    virtual ~strategy() {
        delete m_syntax_tree;
        delete m_modal_tree;
    }

    const z3::sort& get_world_sort() const {
        return m_world_sort;
    }

    z3::expr fresh_world_constant() const {
        return { m_ctx, Z3_mk_fresh_const(m_ctx, "world", m_world_sort) };
    }


    context& ctx() { return m_ctx; }
    
    expr simplify(const expr& e);
    
    check_result check(expr e);
    
    void output_state(std::ostream& ostream);
};
