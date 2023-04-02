#pragma once

#include <unordered_set>
#include <z3++.h>

#include "standard_translation.h"

using namespace z3;

class iterative_deepening : public standard_translation {

    check_result solve(const z3::expr& e) override;

public:

    iterative_deepening(context& ctx, const modal_decls& decls) :
        standard_translation(ctx, decls) {}

};
