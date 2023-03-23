#pragma once

#include <unordered_set>
#include <z3++.h>

#include "assertion.h"
#include "logging.h"
#include "modal_tree.h"
#include "modal_to_euf_base.h"

#if 0

using namespace z3;

struct euf_info : info {
    const z3::func_decl m_aux;
    euf_info(const z3::func_decl& f) : m_aux(f) {}
};

class modal_to_euf : public modal_to_euf_base {
    
    bool is_blast_eq() const override { return true; }
    bool is_nnf() const override { return true; }
    bool is_incremental_parsing() const override { return true; }
    
    static euf_info* info(syntax_tree_node* n) {
        return (euf_info*)n->m_info;
    }
    
    z3::expr_vector apply_syntax_tree() const override;
    
    void prepare_expr(const expr_info &current, expr_vector &args) override;
    
    void output_model(const model& model, std::ostream &ostream) override;
    
public:
    
    modal_to_euf(context& ctx);
};
#endif
