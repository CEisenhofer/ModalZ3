#pragma once

#include <unordered_set>
#include <z3++.h>

#include "assertion.h"
#include "logging.h"
#include "strategy.h"
#include "world.h"

using namespace z3;

class modal_to_prop : public strategy {
    
    class prop_world : public world {
        
        std::unordered_map<func_decl, func_decl> m_func_to_indexed_func;
        
    public:
    
        prop_world(expr_info info) : world(info) {}
        
        expr create_relation(context& ctx, world* world) override {
            DEBUG_CODE(
                for (const auto& r : m_out) {
                    SASSERT(r.first.m_id != world.m_id);
                }
            );
            expr r = expr(ctx, Z3_mk_fresh_const(ctx, (std::string("R") + std::to_string(id()) + "_" + std::to_string(world.id())).c_str(), ctx.bool_sort()));
            add_out(world, r);
            world->add_in(this, r);
            return r;
        }
        
        expr get_atom(const func_decl& decl, const expr_vector& args) override {
            auto it = m_func_to_indexed_func.find(decl);
            if (it == m_func_to_indexed_func.end())
                return it->second(args);
            
            Z3_sort* arr = new Z3_sort[args.size()];
            func_decl indexed_decl = func_decl(decl.ctx(), Z3_mk_fresh_func_decl(decl.ctx(), (decl.name().str() + std::to_string(id())).c_str(), args.size(), arr, decl.range()));
            delete[] arr;
            m_func_to_indexed_func.insert(decl, indexed_decl);
            return decl(args);
        }
    };
    
    func_decl_vector m_uf_list;
    std::unordered_set<std::string> m_uf_set;
    
    std::vector<expr_info> worlds_to_process;
    
    world& get_world(unsigned id, Z3_lbool polarity);
    
    bool is_blast_eq() const override { return true; }
    bool is_nnf() const override { return true; }
    bool is_incremental_parsing() const override { return true; }
    
    void create_app(const expr_info& current, expr_vector &args) override;
    
    void output_model(const model& model, std::ostream &ostream) override;
    
public:
    
    modal_to_prop(context& ctx, bool simplify);
};
