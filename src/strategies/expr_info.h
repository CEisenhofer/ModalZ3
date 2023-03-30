#pragma once
#include "z3++.h"
#include "syntax_tree.h"

using namespace z3;

struct expr_info {
    expr e;
    func_decl decl;
    unsigned arity; // don't use decl.arity()! might fail e.g., for "and"
    
    syntax_tree_node* world;
    
    explicit expr_info(const expr& e) :
        e(e),
        decl(e.decl()),
        arity(e.num_args()),
        world(nullptr) {}
    
    expr_info(const expr_info& other) :
        e(other.e),
        decl(other.decl),
        arity(other.arity),
        world(other.world) {}
    
    expr_info& operator=(const expr_info& other) {
        e = other.e;
        decl = other.decl;
        arity = other.arity;
        world = other.world;
        return *this;
    }
};
