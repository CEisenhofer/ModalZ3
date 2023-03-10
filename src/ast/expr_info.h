#pragma once
#include "z3++.h"

using namespace z3;

class world;

struct expr_info {
    expr e;
    func_decl decl;
    Z3_lbool polarity;
    unsigned arity; // don't use decl.arity()!! 
    
    world* world;
    
    expr_info(const expr& e, Z3_lbool polarity, class world* w) :
        e(e),
        decl(e.decl()),
        polarity(polarity),
        arity(e.num_args()),
        world(w) {}
    
    expr_info(const expr_info& other) :
        e(other.e),
        decl(other.decl),
        polarity(other.polarity),
        arity(other.arity),
        world(other.world) {}
    
    expr_info& operator=(const expr_info& other) {
        e = other.e;
        decl = other.decl;
        polarity = other.polarity;
        arity = other.arity;
        world = other.world;
        return *this;
    }
};