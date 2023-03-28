#include "syntax_tree.h"
#include "lazy_up.h"

z3::expr syntax_tree_node::get_template(bool pos) const {
    if (!pos) {
        return !m_template; // maybe cache for optimization
    }
    return m_template;
}

std::string syntax_tree_node::to_string() const {
    return m_template.to_string();
}
std::string syntax_tree_node::aux_to_string() const {
    return m_aux.to_string();
}

syntax_tree_node* syntax_tree_node::get_child(const z3::expr & e) const {
    auto it = m_expr_to_repr.find(e);
    if (it == m_expr_to_repr.end())
        return nullptr;
    return it->second;
}

z3::expr syntax_tree_node::initialize(const z3::expr & world, bool positive) const {
    SASSERT((z3::ast)m_template);
    SASSERT(world.num_args() == 0);
    z3::expr_vector arg(world.ctx());
    arg.push_back(world);
    return get_template(positive).substitute(arg);
}

syntax_tree::syntax_tree(modal_to_euf_base *base) :
    m_base(base), m_root(new syntax_tree_node(0, nullptr, -1, z3::expr(base->ctx()))) {
    m_nodes.push_back(m_root);
}

syntax_tree_node* syntax_tree::get_root() const {
    return m_root;
}

const z3::sort& syntax_tree::get_world_sort() const {
    return m_base->get_world_sort();
}

syntax_tree_node* syntax_tree::create_node(syntax_tree_node* parent, unsigned relation, const z3::expr& orig_subformula) {
    SASSERT(parent);
    z3::sort domain = get_world_sort();
    Z3_sort z3_domain = domain;
    z3::func_decl decl(ctx(), Z3_mk_fresh_func_decl(ctx(), "Box", 1, &z3_domain, ctx().bool_sort()));
    z3::sort_vector domain_vector(ctx());
    domain_vector.push_back(domain);
    decl = ctx().user_propagate_function(decl.name(), domain_vector, ctx().bool_sort());
    z3::expr x(ctx(), Z3_mk_bound(ctx(), 0, get_world_sort()));

    syntax_tree_node* node = new syntax_tree_node(m_nodes.size(), parent, relation, decl(x));

    parent->m_children.push_back(node);
    parent->m_expr_to_repr[orig_subformula] = node;

    m_func_to_abs[decl] = node;
    m_nodes.push_back(node);
    return node;
}

syntax_tree_node* syntax_tree::get_node(const func_decl& f) {
    return m_func_to_abs[f];
}

z3::context& syntax_tree::ctx() {
    return m_base->ctx();
}

