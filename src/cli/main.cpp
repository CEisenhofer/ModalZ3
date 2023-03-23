#include <iostream>
#include <z3++.h>

#include "modal_to_qeuf.h"
#include "modal_to_euf.h"

using namespace z3;

int main() {
    
    context ctx;
    const expr p = ctx.bool_const("P");
    const expr q = ctx.bool_const("Q");
    const func_decl box = ctx.function("Box", ctx.bool_sort(), ctx.bool_sort());
    const func_decl diamond = ctx.function("Diamond", ctx.bool_sort(), ctx.bool_sort());
    expr e =  diamond(p) && diamond(!p) && box(diamond(diamond(q)));
    modal_to_qeuf transformer(ctx);
    //modal_to_euf transformer(ctx, true);
    transformer.check(e);
    transformer.output_state(std::cout);

    /*
     * for (auto benchmark : my_list_of_fancy_benchmarks) {
     *      strategy1 s1(benchmark);
     *      strategy2 s2(benchmark);
     *      strategy3 s3(benchmark);
     *
     *      stop_watch sw1();
     *      s1.check();
     *      sw1.stop();
     *      s2.check();
     *      s3.check();
     *
     *      std::cout << "Time 1: " << sw1.time() << "\n";
     *      std::cout << "Time 2: " << sw2.time() << "\n";
     *      std::cout << "Time 3: " << sw3.time() << "\n";
     * }
     */
    return 0;
}
