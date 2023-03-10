#pragma once

#include <optional>
#include <stack>
#include <z3++.h>

#include "expr_info.h"
#include "world.h"

using namespace z3;

class strategy {
    
    context& m_ctx;
    world_set m_worlds;
    
    std::stack<std::vector<expr>> m_processed_args;
    std::stack<expr_info> m_apply_list; // m_processed_args.size() == m_apply_list.size() + 1
    unsigned modal_cnt = 0;
    
    std::vector<expr_info> m_modal_list;
    
    const bool m_simplify;
    
    bool is_modal(const func_decl& decl) const;
    
    explicit strategy(context& ctx, bool simplify);
    
    virtual bool is_blast_eq() const { return false; }
    virtual bool is_nnf() const { return false; } // TBD: Implement in simplify
    virtual bool is_incremental_parsing() const { return false; }
    
    expr simplify(const expr& e);
    expr internalize(const expr& e);
    void collect_modals(const expr& e);
    
    void incremental_internalize(const expr& e);
    
    bool simplify(expr_info& current, expr_vector& args);
    
    virtual void create_app(const expr_info& current, expr_vector &args) = 0;
    virtual void add_modal(std::stack<expr_info> &expr_to_process, expr_info &current);
    world* create_world(expr_info &info);
    
    virtual void output_model(const model& model, std::ostream &ostream) = 0;
    
private:
    
    std::optional<solver> m_solver;
    check_result m_last_result;
    
    bool add_children_or_rewrite(std::stack<expr_info>& expr_to_process, expr_info& current, bool analyze);
    
public:
    
    strategy() = delete;
    strategy(const strategy& ctx) = delete;
    
    virtual ~strategy() {}
    
    check_result check(const expr& e);
    
    void output_state(std::ostream &ostream);
};
