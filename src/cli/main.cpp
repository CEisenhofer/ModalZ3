#include <iostream>
#include <z3++.h>

#include "modal_to_qeuf.h"
#include "modal_to_prop.h"

using namespace z3;

int main() {
    
    context ctx;
    const expr p = ctx.bool_const("P");
    const expr q = ctx.bool_const("Q");
    const func_decl box = ctx.function("Box", ctx.bool_sort(), ctx.bool_sort());
    const func_decl diamond = ctx.function("Diamond", ctx.bool_sort(), ctx.bool_sort());
    expr e =  diamond(p) && diamond(!p) && box(diamond(diamond(q)));
    //modal_to_qeuf transformer(ctx);
    modal_to_prop transformer(ctx, true);
    transformer.check(e);
    transformer.output_state(std::cout);
    return 0;
}
