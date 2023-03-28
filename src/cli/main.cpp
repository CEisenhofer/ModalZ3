#include <iterator>
#include <string_view>
#include <vector>

#include <z3++.h>

#include "modal_to_qeuf.h"
#include "modal_to_euf.h"
#include "lazy_up.h"

const char *HELP =
"expects two arguments:\n"
"1. mode: one of 'id' (iterative deepening), TODO more\n"
"2. path to an SMTLIB2 benchmark\n";

// global context
z3::context CTX;
// the boolean sort
z3::sort BOOL_SORT = CTX.bool_sort();
// world sort
z3::sort WORLD_SORT = CTX.uninterpreted_sort("World");
// box and diamond pseudo-operators
z3::func_decl BOX = CTX.function("box", BOOL_SORT, BOOL_SORT);
z3::func_decl DIA = CTX.function("dia", BOOL_SORT, BOOL_SORT);
// world placeholder for parsing
z3::func_decl WORLD = CTX.function("world", z3::sort_vector(CTX), WORLD_SORT);
// the initial world
z3::expr START = CTX.constant("w0", WORLD_SORT);
// reachable predicate
z3::func_decl R = CTX.function("r", WORLD_SORT, WORLD_SORT, BOOL_SORT);

// standard translation, recursive for now
z3::expr standard_translation(unsigned fresh, z3::expr world, z3::expr expr) {
    if(expr.is_app()) {
        unsigned id = expr.decl().id();
        if(id == WORLD.id()) {
            return world;
        }
        else if(id == BOX.id() || id == DIA.id()) {
            std::string name("w");
            name += std::to_string(++fresh);
            z3::expr brave_new = CTX.constant(name.c_str(), WORLD_SORT);
            z3::expr subexpr = standard_translation(fresh, brave_new, expr.arg(0));
            z3::expr reachable = R(world, brave_new);
            if(id == BOX.id())
                return z3::forall(brave_new, z3::implies(reachable, subexpr));
            else 
                return z3::exists(brave_new, reachable && subexpr);
        }
        else {
            z3::expr_vector children(CTX);
            for(const auto &child : expr)
                children.push_back(standard_translation(fresh, world, child));
            return expr.decl()(children);
        }
    }
    else {
        std::cerr << "didn't handle this yet" << std::endl;
        assert(false);
    }
}

void iterative_deepening_mode(const z3::expr_vector &parsed) {
    z3::solver solver(CTX);
    for(const auto &e : parsed)
        solver.add(standard_translation(0, START, e));
    std::cout << solver << std::endl;

    unsigned num_worlds = 1;
    z3::expr world = WORLD();
    z3::expr constraint = world == START;

    while(true) {
        std::cerr << constraint << std::endl;
        std::cerr << "trying size " << num_worlds << "..." << std::endl;
        z3::expr_vector assumptions(CTX);
        assumptions.push_back(z3::forall(WORLD(), constraint));
        if(solver.check(assumptions) == z3::sat) {
            std::cerr << "success!" << std::endl;
            std::cout << solver.get_model() << std::endl;
            return;
        }

        std::string name("w");
        name += std::to_string(num_worlds++);
        z3::expr brave_new = CTX.constant(name.c_str(), WORLD_SORT);
        constraint = constraint || world == brave_new;
    }
}

int main(int argc, char **argv) {
    if(argc != 3) {
        std::cerr << "wrong number of arguments" << std::endl;
        std::cerr << HELP;
        return EXIT_FAILURE;
    }

    std::string_view mode(argv[1]);
    const char *benchmark = argv[2];

    z3::sort_vector sorts(CTX);
    sorts.push_back(WORLD_SORT);
    z3::func_decl_vector functions(CTX);
    functions.push_back(WORLD);
    functions.push_back(BOX);
    functions.push_back(DIA);
    z3::expr_vector parsed = CTX.parse_file(benchmark, sorts, functions);

    if(mode == "id")
        iterative_deepening_mode(parsed);
    else {
        std::cerr << "unknown mode: " << mode << std::endl;
        std::cerr << HELP;
        return EXIT_FAILURE;
    }
    /*
    context ctx;
    const expr p = ctx.bool_const("P");
    const expr q = ctx.bool_const("Q");
    const func_decl box = ctx.function("Box", ctx.bool_sort(), ctx.bool_sort());
    const func_decl diamond = ctx.function("Diamond", ctx.bool_sort(), ctx.bool_sort());
    expr e =  diamond(p) && diamond(!p) && box(diamond(diamond(q)));
    //modal_to_qeuf transformer(ctx);
    //modal_to_euf transformer(ctx);

    e = diamond(p);
    lazy_up transformer(ctx);
    transformer.check(e);
    transformer.output_state(std::cout);
    */

    /*
     * Michael: we don't need this, just use command-line tools
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
