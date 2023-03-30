#include <iterator>
#include <string_view>
#include <vector>
#include <z3++.h>

#include "iterative_deepening.h"
#include "lazy_up.h"
#include "modal_to_euf.h"
#include "standard_translation.h"

const char* HELP =
" Mode File\n"
"Solves a multi-modal formula\n\n"
"Mode\t one of: std (std translation), id (iterative deepening), upl (user-propagator; lazy), upe (user-propagator; eager)\n"
"File\t Path to an SMTLIB2 benchmark\n";

int main(int argc, char **argv) {
    if(argc != 3) {
        std::cerr << "wrong number of arguments" << std::endl;
        std::cerr << argv[0] << HELP;
        return EXIT_FAILURE;
    }

    std::string_view mode(argv[1]);
    const char* benchmark = argv[2];

    z3::context ctx;
    z3::sort world_sort = ctx.uninterpreted_sort("World");
    z3::sort relation_sort = ctx.uninterpreted_sort("Relation");
    z3::sort_vector domain(ctx);
    z3::func_decl placeholder = ctx.function("world", domain, world_sort);
    domain.push_back(relation_sort);
    domain.push_back(ctx.bool_sort());
    z3::func_decl dia = ctx.function("dia", domain, ctx.bool_sort());
    z3::func_decl box = ctx.function("box", domain, ctx.bool_sort());
    
    domain.pop_back();
    domain.push_back(world_sort);
    domain.push_back(world_sort);
    z3::func_decl reachable = ctx.function("reachable", domain, ctx.bool_sort());

    z3::sort_vector sorts(ctx);
    sorts.push_back(world_sort);
    sorts.push_back(relation_sort);
    z3::func_decl_vector functions(ctx);
    functions.push_back(box);
    functions.push_back(dia);
    functions.push_back(placeholder);
    z3::expr_vector parsed = ctx.parse_file(benchmark, sorts, functions);

    auto id  = [&world_sort, &relation_sort, &dia, &box, &reachable, &placeholder](z3::context& ctx) { return new iterative_deepening(ctx, world_sort, relation_sort, dia, box, reachable, placeholder()); };
    auto std = [&world_sort, &relation_sort, &dia, &box, &reachable, &placeholder](z3::context& ctx) { return new standard_translation(ctx, world_sort, relation_sort, dia, box, reachable, placeholder()); };
    auto upl = [&world_sort, &relation_sort, &dia, &box, &reachable, &placeholder](z3::context& ctx) { return new lazy_up(ctx, world_sort, relation_sort, dia, box, reachable, placeholder()); };

    std::unordered_map<std::string_view, std::function<strategy*(z3::context&)>> mapping =
    {
        { "id",  id  },
        { "std", std },
        { "upl", upl },
    };

    auto it = mapping.find(mode);
    if (it == mapping.end()) {
        std::cerr << "unknown mode: " << mode << std::endl;
        std::cerr << HELP;
        return EXIT_FAILURE;
    }
    strategy* str = it->second(ctx);
    str->check(z3::mk_and(parsed));
    str->output_state(std::cout);
    delete str;
    
    return 0;
}
