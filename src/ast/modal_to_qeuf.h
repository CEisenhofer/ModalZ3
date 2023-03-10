#pragma once

#include <unordered_set>
#include <z3++.h>

#include "logging.h"
#include "strategy.h"

using namespace z3;

class modal_to_qeuf : public strategy {

    const char* world_sort_name = "Worlds";
    const char* worlds_name = "World";
    
    sort m_world_sort;
    expr_vector m_world_variables; // by id
    func_decl_vector m_relation;
    
    func_decl_vector m_uf_list;
    std::unordered_set<std::string> m_uf_set;
    
    expr get_world(unsigned id);
    
    void create_app(const expr_info& current, expr_vector &args) override;
    
    void output_model(const model& model, std::ostream &ostream) override;
    
public:
    
    modal_to_qeuf(context& ctx, bool simplify);
    
};
