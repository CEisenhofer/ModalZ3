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
    bool basic_ctx; // is the currently evaluated expression boolean?

    syntax_tree_node* abs;
    
    explicit expr_info(const expr& e) :
        e(e),
        decl(e.decl()),
        arity(e.num_args()),
        top_level(false),
        no_scope(false),
        basic_ctx(true),
        abs(nullptr) {}
    
    expr_info(const expr_info& other) :
        e(other.e),
        decl(other.decl),
        arity(other.arity),
        top_level(other.top_level),
        no_scope(other.no_scope),
        basic_ctx(other.basic_ctx),
        abs(other.abs) {}
    
    expr_info& operator=(const expr_info& other) {
        e = other.e;
        decl = other.decl;
        arity = other.arity;
        top_level = other.top_level;
        no_scope = other.no_scope;
        basic_ctx = other.basic_ctx;
        abs = other.abs;
        return *this;
    }
};
