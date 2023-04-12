#pragma once
#include "z3++.h"
#include "syntax_tree.h"

using namespace z3;

struct expr_info {
    expr e;
    func_decl decl;
    unsigned arity; // don't use decl.arity()! might fail e.g., for "and"
    bool top_level; // directly after assert or a conjunction in assert
    bool no_scope; // not in the scope of a modal operator or similar

    syntax_tree_node* world;
    
    explicit expr_info(const expr& e) :
        e(e),
        decl(e.decl()),
        arity(e.num_args()),
        top_level(false),
        no_scope(false),
        world(nullptr) {}
    
    expr_info(const expr_info& other) :
        e(other.e),
        decl(other.decl),
        arity(other.arity),
        top_level(other.top_level),
        no_scope(other.no_scope),
        world(other.world) {}
    
    expr_info& operator=(const expr_info& other) {
        e = other.e;
        decl = other.decl;
        arity = other.arity;
        top_level = other.top_level;
        no_scope = other.no_scope;
        world = other.world;
        return *this;
    }
};
