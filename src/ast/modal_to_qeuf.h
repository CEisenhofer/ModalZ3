#pragma once

#include <unordered_set>
#include <z3++.h>

#include "logging.h"
#include "strategy.h"
#include "modal_to_euf_base.h"

using namespace z3;

class modal_to_qeuf : public modal_to_euf_base {

    expr_vector m_world_variables; // by id
    
    expr get_world(unsigned id);
    
    void prepare_expr(const expr_info &current, expr_vector &args) override;
    
    void output_model(const model& model, std::ostream &ostream) override;
    
public:
    
    modal_to_qeuf(context& ctx);
    
};
