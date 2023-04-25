#include <cstring>
#include <iostream>
#include <fstream>
#include <thread>

#include "iterative_deepening_quant.h"
#include "lazy_up.h"
#include "random_formula.h"
#include "standard_translation.h"

constexpr unsigned RANDOM_FORMULAS = 10000;
constexpr unsigned MAX_RELATIONS = 3;

unsigned cnt_str(const std::string& s, const std::string& target) {
   int cnt = 0;
   std::string::size_type pos = 0;
   while ((pos = s.find(target, pos)) != std::string::npos) {
          cnt++;
          pos += target.length();
   }
   return cnt;
}

struct args {
    unsigned min_relations = 1;
    unsigned max_relations = MAX_RELATIONS;
    unsigned repetitions = RANDOM_FORMULAS;
    unsigned min_modals = 2;
    unsigned max_modals = 5;
    unsigned min_length = 100;
    unsigned max_length = 500;
    unsigned max_depth = 5;
};

void test(int idx, const args& args) {

    context ctx;
    modal_decls decls = modal_decls::create_default(ctx);

    //std::vector<int> world_cnt[3]; // some statistics
    unsigned world_cnt[3]; // some statistics
    std::vector<unsigned> time[3]; // some statistics
    memset(world_cnt, 0, sizeof(unsigned) * 3);

    for (unsigned r = args.min_relations; r <= args.max_relations; r++) {
        random_formula rf(ctx, decls, r);
        rf.set_max_depth(args.max_depth);
        
#if 0
        for (unsigned i = 0; i < RANDOM_FORMULAS; i++) {
            if (i % 100 == 0) 
                    std::cout << "Iteration " << i << std::endl; 
            expr e = rf.get();
            
            preprocess_only preprocess(ctx);
            expr preprocessed = preprocess.rewrite_formula(e);
            
            modal_to_qeuf std_translation1(ctx, false);
            check_result result = std_translation1.check(!implies(e, preprocessed));
            if (result != z3::unsat) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "Preprocessed " << preprocessed << " is weaker than " << e << std::endl;
                exit(-1);
            }
            
            modal_to_qeuf std_translation2(ctx, false);
            result = std_translation2.check(!implies(preprocessed, e));
            if (result != z3::unsat) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "Original " << preprocessed << " is weaker than " << e << std::endl;
                exit(1);
            }
        }
        
        std::cout << "Preprocessing succeeded!\n\n";
#endif
        
        for (unsigned i = 0; i < args.repetitions; i++) {
            if (idx < 0 && i % 10 == 0)
                std::cout << "Iteration " << i << std::endl;
            rep:
            expr e = rf.get();
            {
                standard_translation simplifier(ctx, decls);
                e = simplifier.simplify(e);

                if (e.to_string().length() < args.min_length
                || e.to_string().length() > args.max_length
                || cnt_str(e.to_string(), "box") < args.min_modals
                || cnt_str(e.to_string(), "box") > args.max_modals
                ) // hopefully avoid trivial examples
                    goto rep;
            }

            //std::cout << e << "\n\n" << std::endl;

            standard_translation std_translation(ctx, decls);
            std_translation.set_is_benchmark(true);
            check_result result_std_translation = std_translation.check(e);
            
            iterative_deepening_quant iterative_deepening(ctx, decls);
            iterative_deepening.set_is_benchmark(true);
            check_result result_iterative_deepening = iterative_deepening.check(e);

            lazy_up lazy_up(ctx, decls);
            lazy_up.set_is_benchmark(true);
            check_result result_lazy_up = lazy_up.check(e);
    
            if (result_std_translation == z3::unknown) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "std-translation unknown: " << e << std::endl;
                exit(-1);
            }
            
            if (result_iterative_deepening == z3::unknown) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "iterative-deepening unknown: " << e << std::endl;
                exit(-1);
            }
            
            if (result_lazy_up == z3::unknown) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "lazy-up unknown: " << e << std::endl;
                exit(-1);
            }
            
            if (result_std_translation != result_lazy_up) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "Different results: std (" << result_std_translation << ") vs lazy-up (" << result_lazy_up << "): " << e << std::endl;
                exit(-1);
            }
            if (result_std_translation != result_iterative_deepening) {
                std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                std::cerr << "Different results: std (" << result_std_translation << ") vs lazy-up (" << result_iterative_deepening << "): " << e << std::endl;
                exit(-1);
            }
            if (result_lazy_up == z3::sat) {
                if (lazy_up.model_check(e) != Z3_L_TRUE) {
                    std::cerr << "Seed: " << rf.get_last_seed() << ":\n";
                    std::cerr << "Verification failure: " << e << ":\n";
                    std::cerr << "\"Model\":\n";
                    lazy_up.output_state(std::cerr);

                    exit(-1);
                }
            }

            time[0].push_back(std_translation.solving_time().count());
            time[1].push_back(iterative_deepening.solving_time().count());
            time[2].push_back(lazy_up.solving_time().count());

            if (idx < 0) {
                std::cout << std_translation.solving_time().count() << " STD" << std::endl;
                std::cout << iterative_deepening.solving_time().count() << " ID" << std::endl;
                std::cout << lazy_up.solving_time().count() << " UP" << std::endl;
            }
            
            if (result_std_translation == sat) {
                /*world_cnt[0].push_back(std_translation.domain_size());
                world_cnt[1].push_back(iterative_deepening.domain_size());
                world_cnt[2].push_back(lazy_up.domain_size());*/

                world_cnt[0] += std_translation.domain_size();
                world_cnt[1] += iterative_deepening.domain_size();
                world_cnt[2] += lazy_up.domain_size();
            }
        }
    }

    std::cout << "Thread " << abs(idx) << " finished\n";

    if (idx < 0) {
        std::cout << "World counts:\n";
        std::cout << "STD: " << world_cnt[0] << std::endl;
        std::cout << "ID : " << world_cnt[1] << std::endl;
        std::cout << "UPE: " << world_cnt[2] << std::endl;
    }
    else {
        std::ofstream out((std::string("out") + std::to_string(idx) + ".txt").c_str());
        for (unsigned i = 0; i < args.repetitions; i++)
            out << time[0][i] << ";" << time[1][i] << ";" << time[2][i] << "\n";
        out.close();
    }
}

#define ERROR do { std::cout << "Could not parse command lines.\n" << "Usage: [-file] [-min_rel=x] [-max_rel=x] [-rep=x] [-min_modals=x] [-max_modals=x] [-min_length=x] [-max_length=x]" << std::endl; exit(-1); } while(false)

int main(int argc, char** argv) {
    unsigned start = 1;
    unsigned threads = 1;
    bool file = false;

    args args;
    // -threads=4 -rep=100 -min_modals=2 -max_modals=5 -min_length=100 -max_length=500
    for (; start < argc; start++) {
        if (strncmp(argv[start], "-file", 5) == 0) {
            file = true;
            continue;
        }
        if (strncmp(argv[start], "-threads=", 9) == 0) {
            threads = atoi(argv[start] + 9);
            continue;
        }
        if (strncmp(argv[start], "-min_rel=", 9) == 0) {
            args.min_relations = atoi(argv[start] + 9);
            continue;
        }
        if (strncmp(argv[start], "-max_rel=", 9) == 0) {
            args.max_relations = atoi(argv[start] + 9);
            continue;
        }
        if (strncmp(argv[start], "-rep=", 5) == 0) {
            args.repetitions = atoi(argv[start] + 5);
            continue;
        }
        if (strncmp(argv[start], "-min_modals=", 12) == 0) {
            args.min_modals = atoi(argv[start] + 12);
            continue;
        }
        if (strncmp(argv[start], "-max_modals=", 12) == 0) {
            args.max_modals = atoi(argv[start] + 12);
            continue;
        }
        if (strncmp(argv[start], "-min_length=", 12) == 0) {
            args.min_length = atoi(argv[start] + 12);
            continue;
        }
        if (strncmp(argv[start], "-max_length=", 12) == 0) {
            args.max_length = atoi(argv[start] + 12);
            continue;
        }
        if (strncmp(argv[start], "-max_depth=", 11) == 0) {
            args.max_depth = atoi(argv[start] + 11);
            continue;
        }
        ERROR;
    }

    std::cout
        << "Running:\n"
        << "File:" << file << "\n"
        << "Repetitions: " << args.repetitions << " on " << threads << " threads\n"
        << "Length: [" << args.min_length << "; " << args.max_length << "]\n"
        << "Relations: [" << args.min_relations << "; " << args.max_relations << "]\n"
        << "Modalities: [" << args.min_modals << "; " << args.max_modals << "]\n"
        << "Max Depth: " << args.max_depth << "\n"
        << std::endl;

    if (
            args.min_length > args.max_length ||
            args.min_modals > args.max_modals ||
            args.min_relations > args.max_relations ||
            args.min_modals < 0 || args.min_length < 0 || args.min_relations < 0
    ) {
        ERROR;
    }

    std::vector<std::thread> thread_list;

    for (unsigned i = 0; i < threads; i++) {
        std::thread thread(test, file ? i + 1 : -(i + 1), args);
        thread_list.push_back(std::move(thread));
    }
    for (unsigned i = 0; i < threads; i++) {
        thread_list[i].join();
    }
    return 0;
}
