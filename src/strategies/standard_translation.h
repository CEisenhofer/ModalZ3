#pragma once

#include <unordered_set>
#include <z3++.h>

#include "logging.h"
#include "strategy.h"

using namespace z3;

class standard_translation : public strategy {

    expr_vector m_variables;
    func_decl m_reachable;
    
    expr create_formula(const expr& e) override;

    void output_model(const model& model, std::ostream &ostream) override;
    
public:
    
    standard_translation(context& ctx, const modal_decls& decls);

    virtual unsigned domain_size() override;
};
