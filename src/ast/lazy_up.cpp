#include "lazy_up.h"

void assignment_undo::undo() {
    m_world->unassign(m_var);
}

void create_world_undo::undo() {
    m_parent_world->remove_and_delete_last_child();
}

unsigned lazy_up::get_variable(const func_decl& decl) {
    std::string name = decl.name().str();
    auto it = m_str_to_var.find(name);
    SASSERT(it != m_str_to_var.end());
    return it->second;
}

void lazy_up::fixed(const expr& e, const expr& value) {
    SASSERT(value.is_bool());
    bool v = value.is_true();
    func_decl func = e.decl();
    SASSERT(func.arity() > 0);
    expr arg = e.arg(func.arity() - 1);
    SASSERT(z3::eq(arg.get_sort(), m_world_sort));
    modal_tree_node* world = m_modal_tree->get(arg);
    unsigned var = get_variable(arg.decl());
    m_trail.push(new assignment_undo(world, var));
}
