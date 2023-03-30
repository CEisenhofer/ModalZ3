#pragma once

#include <unordered_set>
#include <z3++.h>

#include "standard_translation.h"

using namespace z3;

class iterative_deepening : public standard_translation {

    check_result solve(const z3::expr& e) override;

public:

    iterative_deepening(context& ctx, const sort& world_sort, const sort& reachability_sort, const func_decl& dia, const func_decl& box, const func_decl& reachable, const expr& placeholder) :
        standard_translation(ctx, world_sort, reachability_sort, dia, box, reachable, placeholder) {}

};
