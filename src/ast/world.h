#pragma once
#include "expr_info.h"
#include "assertion.h"

class world {
    
protected:
    
    expr_info m_operator; // modal operator generating this world
    world* parent; // the world in which the modal operator was evaluated which resulted in this world. This world should also occur in the in-set
    std::vector<std::pair<world*, expr /* justifying atom */>> m_out;
    std::vector<std::pair<world*, expr /* justifying atom */>> m_in;
    
public:
    
    world(expr_info info) : m_operator(info) {}
    
    virtual ~world() {}
    
    virtual expr create_relation(context& ctx, world *world) { VERIFY(false); return expr(ctx); }
    virtual expr get_atom(const func_decl& decl, const expr_vector& args) { VERIFY(false); return expr(decl.ctx()); }
    
    void add_out(const world* w, const expr& e) {
        m_out.emplace_back(w, e);
    }
    
    void add_in(const world* w, const expr& e) {
        m_in.emplace_back(w, e);
    }
    
    unsigned id() const {
        return m_operator.modal_id;
    }
    
    unsigned contained_id() const {
        return m_operator.contained_modal_id;
    }
    
    Z3_lbool polarity() const {
        return m_operator.polarity;
    }
};

class world_set {
    
    std::vector<world*> m_worlds;
    
public:
    
    ~world_set() {
        for (auto& world : m_worlds)
            delete world;
    }
    
    world& get_or_create(unsigned id, world* w) {
        SASSERT(w->id() == id);
        if (id >= m_worlds.size()) {
            m_worlds.resize(id + 1);
        }
        if (!m_worlds[id])
            m_worlds[id] = w;
        else 
            delete w;
        
        return *m_worlds[id];
    }
    
    world& get(unsigned id) {
        SASSERT(id < m_worlds.size());
        SASSERT(m_worlds[id]);
        return *m_worlds[id];
    }
    
};
