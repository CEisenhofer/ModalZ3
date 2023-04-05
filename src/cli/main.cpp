#include <iterator>
#include <filesystem>
#include <string_view>
#include <vector>
#include <z3++.h>

#include "iterative_deepening_quant.h"
#include "lazy_up.h"
#include "standard_translation.h"

const char* HELP =
" Mode File\n"
"Solves a multi-modal formula\n\n"
"Mode\t one of: std (std translation), id (iterative deepening), upl (user-propagator; lazy), upe (user-propagator; eager)\n"
"File\t Path to an SMTLIB2 set_is_benchmark\n";

int main(int argc, char **argv) {
    if(argc != 3) {
        std::cerr << "wrong number of arguments" << std::endl;
        std::cerr << argv[0] << HELP;
        return EXIT_FAILURE;
    }
    std::string_view mode(argv[1]);
    const char* path = argv[2];
    std::vector<std::string> paths;
    
    if (!std::filesystem::exists(path)) {
        std::cerr << "path does not exist" << std::endl;
        std::cerr << argv[0] << HELP;
        return EXIT_FAILURE;
    }
    
    if (std::filesystem::is_directory(path)) {
        for (const auto& entry : std::filesystem::directory_iterator(path)) {
            std::string ext = entry.path().extension().string();
            if (entry.is_regular_file() && ext == ".smt2")
                paths.push_back(entry.path().string());
        }
    }
    else {
        paths.emplace_back(path);
    }
    
    for (const std::string& input : paths) {
    
        std::cout << "Input: " << input << std::endl; 

        /*Z3_enable_trace("rewriter");
        Z3_enable_trace("rewriter_visit");
        Z3_enable_trace("rewriter_subst");
        Z3_enable_trace("reduce_app");
        Z3_enable_trace("reduce_quantifier");
        Z3_enable_trace("rewriter_reuse");
        Z3_enable_trace("rewriter_step");
        Z3_enable_trace("elim_unused_vars");*/
        
        /*z3::set_param("sat.euf", true);
        z3::set_param("sat.smt", true);
        z3::config cfg;
        cfg.set("sat.smt", true);
        cfg.set("sat.euf", true);
        z3::context ctx(cfg);*/
        z3::context ctx;
        modal_decls decls(ctx.uninterpreted_sort("World"), ctx.uninterpreted_sort("Relation"));
        z3::sort_vector domain(ctx);
        func_decl placeholder = ctx.function("world", domain, decls.world_sort);
        decls.placeholder = placeholder;
        domain.push_back(decls.relation_sort);
        domain.push_back(ctx.bool_sort());
        decls.dia = ctx.function("dia", domain, ctx.bool_sort());
        decls.box = ctx.function("box", domain, ctx.bool_sort());
        
        domain.pop_back();
        domain.push_back(decls.world_sort);
        domain.push_back(ctx.bool_sort());
        decls.local = ctx.function("local", domain, ctx.bool_sort());
        decls.global = ctx.function("global", ctx.bool_sort(), ctx.bool_sort());
        
        z3::expr_vector parsed = ctx.parse_file(input.c_str(), decls.get_sorts(), decls.get_decls());
    
        auto id  = [&decls](z3::context& ctx) { return new iterative_deepening_quant(ctx, decls); };
        auto std = [&decls](z3::context& ctx) { return new standard_translation(ctx, decls); };
        auto upl = [&decls](z3::context& ctx) { return new lazy_up(ctx, decls); };
    
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
        check_result res = str->check(z3::mk_and(parsed));
        str->output_state(std::cout);
        
        if (mode == "upl" && res == z3::sat) {
            if (str->model_check(z3::mk_and(parsed)) != Z3_L_TRUE) {
                std::cout << "FAILED to check model" << std::endl;
            }
            else {
                std::cout << "SUCCESSFULLY checked model" << std::endl;
            }
        }
        
        delete str;
    }
    
    return 0;
}
