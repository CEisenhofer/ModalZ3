#pragma once

#include <optional>
#include <stack>
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
    std::stack<expr_info> m_apply_list; // m_processed_args.size() == m_apply_list.size() + 1

    check_result m_last_result;
    
    bool is_modal(const func_decl& decl) const;
    
    explicit strategy(context& ctx);
    
    virtual bool is_blast_eq() const { return false; }
    virtual bool is_nnf() const { return false; } // TBD: Implement in simplify
    virtual bool is_incremental_parsing() const { return false; }
    
    expr simplify_formula(const expr& e);
    virtual expr create_formula(const expr& e) = 0;

    virtual void output_model(const model& model, std::ostream &ostream) = 0;
    
    bool post_rewrite(expr_info& current, expr_vector& args);
    bool pre_rewrite(std::stack<expr_info>& expr_to_process, expr_info& current);

public:
    
    strategy() = delete;
    strategy(const strategy& ctx) = delete;
    
    virtual ~strategy() {
        delete m_syntax_tree;
        delete m_modal_tree;
    }

    context& ctx() { return m_ctx; }
    
    expr simplify(const expr& e);
    
    check_result check(expr e);
    
    void output_state(std::ostream& ostream);
};
