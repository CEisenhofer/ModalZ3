#include <cstring>
#include <iterator>
#include <filesystem>
#include <fstream>
#include <set>
#include <string_view>
#include <vector>
#include <z3++.h>

#include "iterative_deepening_quant.h"
#include "iterative_deepening_unrolled.h"
#include "lazy_up.h"
#include "standard_translation.h"
#include "parse_exception.h"

const char* HELP =
" [-m=size_in_mb] [-t=timeout_in_ms] [-r] [-l=log_file] Mode File\n"
"Solves a multi-modal formula\n\n"
"Mode\t one of: std (std translation), id (iterative deepening), id2 (iterative deepening with unrolling), upl (user-propagator; lazy) [use \"upl\"; the other are for comparison only]\n"
"File\t Path to an SMTLIB2 set_is_benchmark\n";

int main(int argc, char** argv) {

    unsigned start = 1;
    unsigned limit_mem = 0;
    unsigned limit_time = 0;
    std::string log_file;
    bool recursive = false;
    for (; start < argc; start++) {
        if (strncmp(argv[start], "-m=", 3) == 0) {
            limit_mem = atoi(argv[start] + 3);
            continue;
        }
        if (strncmp(argv[start], "-t=", 3) == 0) {
            limit_time = atoi(argv[start] + 3);
            continue;
        }
        if (strncmp(argv[start], "-r", 2) == 0) {
            recursive = true;
            continue;
        }
        if (strncmp(argv[start], "-l=", 3) == 0) {
            log_file = argv[start] + 3;
            if (log_file.starts_with('"'))
                log_file = log_file.substr(1);
            if (log_file.ends_with('"'))
                log_file.pop_back();
            continue;
        }
        break;
    }
    if (argc - start != 2) {
        std::cerr << "wrong number of mandatory arguments: " << argc - start << std::endl;
        for (; start < argc; start++) {
            std::cerr << "\t" << argv[start] << std::endl;
        }
        std::cerr << argv[0] << HELP;
        return EXIT_FAILURE;
    }
    std::string_view mode(argv[start]);
    const char* path = argv[start + 1];
    std::set<std::string> paths;
    std::set<std::filesystem::path> to_explore;
    
    if (!std::filesystem::exists(path)) {
        std::cerr << "path does not exist" << std::endl;
        std::cerr << argv[0] << HELP;
        return EXIT_FAILURE;
    }
    
    if (std::filesystem::is_directory(path)) {
        to_explore.insert(path);
        while (!to_explore.empty()) {
            std::filesystem::path current = *to_explore.begin();
            to_explore.erase(to_explore.begin());
            for (const auto& entry : std::filesystem::directory_iterator(current)) {
                if (entry.is_directory()) {
                    if (recursive)
                        to_explore.insert(entry.path());
                }
                else {
                    std::string ext = entry.path().extension().string();
                    if (entry.is_regular_file() && ext == ".smt2")
                        paths.insert(entry.path().string());
                }
            }
        }
    }
    else {
        paths.insert(path);
    }

    std::ofstream* out = nullptr;
    if (!log_file.empty()) {
        std::cout << "Putting results to " << log_file << std::endl;
        try {
            out = new std::ofstream(log_file);
        } catch (std::exception& e) {
            std::cerr << "Could not create log-file" << std::endl;
            return -1;
        }
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
        
        //z3::set_param("sat.euf", true);
        //z3::set_param("sat.smt", true);
        z3::context ctx;
        modal_decls decls = modal_decls::create_default(ctx);
        
        z3::expr_vector parsed = z3::expr_vector(ctx);
        try {
            parsed = ctx.parse_file(input.c_str(), decls.get_sorts(), decls.get_decls());
        }
        catch (const exception& e) {
            std::cerr << "Parsing failed: " << e.msg() << std::endl;
            continue;
        }
    
        auto id  = [&decls](z3::context& ctx) { return new iterative_deepening_quant(ctx, decls); };
        auto id2 = [&decls](z3::context& ctx) { return new iterative_deepening_unrolled(ctx, decls); };
        auto std = [&decls](z3::context& ctx) { return new standard_translation(ctx, decls); };
        auto upl = [&decls](z3::context& ctx) { return new lazy_up(ctx, decls); };
    
        std::unordered_map<std::string_view, std::function<strategy*(z3::context&)>> mapping =
        {
            { "id",  id  },
            { "id2",  id2  },
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
        str->set_is_benchmark(true);
        if (limit_time)
            str->set_timeout(limit_time);
        if (limit_mem)
            str->set_memout(limit_mem);
        try {
            if (out)
                *out << input.c_str() << ";";
            check_result res = str->check(z3::mk_and(parsed));
            str->output_state(std::cout);
            if (out) {
                if (res == z3::unknown)
                    *out << "-1;-1\n";
                else if (res == z3::unsat)
                    *out << str->solving_time().count() << ";0\n";
                else
                    *out << str->solving_time().count() << ";" << str->domain_size() << "\n";
            }
            std::cout << "Solving-Time: " << str->solving_time().count() << std::endl;

            if (mode == "upl" && res == z3::sat) {
                if (str->model_check(z3::mk_and(parsed)) != Z3_L_TRUE) {
                    std::cout << "FAILED to check model" << std::endl;
                }
                else {
                    std::cout << "SUCCESSFULLY checked model" << std::endl;
                }
            }
        } catch (const parse_exception& e) {
            delete str;
            std::cerr << "Error: " << e.what() << std::endl;
            if (out) {
                *out << "Crashed!\n";
                delete out;
            }
            return -1;
        }

#if 0
        // For comparison
        standard_translation check(ctx, decls);
        check_result res_comp = check.check(z3::mk_and(parsed));
        if (res != res_comp) {
            std::cerr << "Different results: "
            << (res == check_result::sat ? "sat" : res == check_result::unsat ? "unsat" : "unknown" )
            << " vs. "
            << (res_comp == check_result::sat ? "sat" : res_comp == check_result::unsat ? "unsat" : "unknown" ) << std::endl;
        }
        else {
            std::cout << "Results coincide" << std::endl;
        }
#endif
        
        delete str;
    }

    if (out)
        delete out;

    return 0;
}
