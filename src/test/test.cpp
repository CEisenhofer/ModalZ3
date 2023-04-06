#include <cstring>
#include <iostream>

#include "iterative_deepening_quant.h"
#include "lazy_up.h"
#include "random_formula.h"
#include "standard_translation.h"

constexpr unsigned RANDOM_FORMULAS = 300;
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

void test() {
    context ctx;

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

    //std::vector<int> world_cnt[3]; // some statistics
    unsigned world_cnt[3]; // some statistics
    memset(world_cnt, 0, sizeof(unsigned) * 3);

    for (unsigned r = 1; r <= MAX_RELATIONS; r++) {
        random_formula rf(ctx, decls, r);
        rf.set_max_depth(6);
        
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
        
        for (unsigned i = 0; i < RANDOM_FORMULAS; i++) {
            if (i % 100 == 0) 
                std::cout << "Iteration " << i << std::endl; 
            rep:
            expr e = rf.get();
            {
                standard_translation simplifier(ctx, decls);
                e = simplifier.simplify(e);

                if (e.to_string().length() < 20
                //|| e.to_string().length() > 100
                || cnt_str(e.to_string(), "box") < 2
                ) // hopefully avoid trivial examples
                    goto rep;
            }

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

#if 0
            std::cout << std_translation.solving_time().count() << " STD" << std::endl;
            std::cout << iterative_deepening.solving_time().count() << " ID" << std::endl;
            std::cout << lazy_up.solving_time().count() << " UP" << std::endl;
#endif
            
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

    std::cout << "STD: " << world_cnt[0] << std::endl;
    std::cout << "ID : " << world_cnt[1] << std::endl;
    std::cout << "UPE: " << world_cnt[2] << std::endl;
}

int main() {
    test();
    return 0;
}
