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

    expr create_formula(const expr& e) override;

    void output_model(const model& model, std::ostream &ostream) override;
    
public:
    
    modal_to_qeuf(context& ctx);
    
};
