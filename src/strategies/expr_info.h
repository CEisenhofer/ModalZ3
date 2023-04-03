#pragma once
#include "z3++.h"
#include "syntax_tree.h"

using namespace z3;

struct expr_info {
    expr e;
    func_decl decl;
    unsigned arity; // don't use decl.arity()! might fail e.g., for "and"
    bool top_level;
    
    syntax_tree_node* world;
    
    explicit expr_info(const expr& e) :
        e(e),
        decl(e.decl()),
        arity(e.num_args()),
        top_level(false),
        world(nullptr) {}
    
    expr_info(const expr_info& other) :
        e(other.e),
        decl(other.decl),
        arity(other.arity),
        top_level(other.top_level),
        world(other.world) {}
    
    expr_info& operator=(const expr_info& other) {
        e = other.e;
        decl = other.decl;
        arity = other.arity;
        top_level = other.top_level;
        world = other.world;
        return *this;
    }
};
