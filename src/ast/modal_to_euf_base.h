#pragma once

#include <unordered_set>
#include <z3++.h>

#include "logging.h"
#include "strategy.h"

using namespace z3;

class modal_to_euf_base : public strategy {

protected:
    
    const char* world_sort_name = "Worlds";
    
    sort m_world_sort;
    func_decl_vector m_relation;
    func_decl_vector m_uf_list;
    std::unordered_set<func_decl, func_decl_hash, func_decl_eq> m_uf_set;
    std::unordered_map<func_decl, unsigned, func_decl_hash, func_decl_eq> m_uf_to_id;

public:

    modal_to_euf_base(context& ctx) : 
        strategy(ctx), 
        m_world_sort(ctx.uninterpreted_sort(world_sort_name)),
        m_relation(ctx),
        m_uf_list(ctx) {
    
        m_relation.push_back(ctx.function("R", m_world_sort, m_world_sort, ctx.bool_sort())); // TODO: Muli-Modal
    }

    const z3::sort& get_world_sort() const {
        return m_world_sort;
    }
    
    z3::expr get_world_constant(unsigned id) const {
        return m_ctx.constant(("world" + std::to_string(id)).c_str(), m_world_sort);
    }
    
};
