#pragma once

#include <z3++.h>

#include "strategy.h"

using namespace z3;

class preprocess_only : public strategy {

    bool is_blast_eq() const override { return true; }
    bool is_nnf() const override { return true; }
    
    void create_app(const expr_info& current, expr_vector &args) { m_processed_args.top().push_back(current.decl(args)); }
    
    void output_model(const model& model, std::ostream &ostream) { ostream << model.to_string() << "\n"; }
    
public:
    
    preprocess_only(context& ctx) : strategy(ctx, true) {}
    
    expr internalize(const expr& e) override {
        return strategy::internalize(e);
    }
    
};
