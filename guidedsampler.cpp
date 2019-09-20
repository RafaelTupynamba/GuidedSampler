#include <string.h>
#include <z3++.h>
#include <vector>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <fstream>

enum {
STRAT_SMTBIT,
STRAT_SMTBV,
STRAT_SAT,
STRAT_PRED_HARD,
STRAT_PRED_SOFT,
STRAT_FLIP_PREDS,
STRAT_REMOVE_REPEATED,
STRAT_RANDOM_SOFT_PREDS
};

struct coverage_small {
    unsigned long c0;
    unsigned long c1;
};

struct coverage_big {
    std::vector<bool> c0;
    std::vector<bool> c1;
};

struct coverage_struct {
    struct coverage_small s;
    struct coverage_big b;
    int index;
};

typedef struct coverage_struct coverage;

struct coverage_count_struct {
    int c0;
    int c1;
};

typedef struct coverage_count_struct coverage_count;

struct pair_hash {
    inline std::size_t operator()(const std::pair<int,int> & v) const {
        return v.first*31+v.second;
    }
};

extern bool get_coverage_vector;
extern std::vector<coverage_count> coverage_vector;


extern int coverage_enable;
extern int coverage_bool;
extern int coverage_bv;
extern int coverage_all_bool;
extern int coverage_all_bv;
extern std::unordered_map<Z3_ast, coverage> covered;

Z3_ast parse_bv(char const * n, Z3_sort s, Z3_context ctx);
std::string bv_string(Z3_ast ast, Z3_context ctx);

typedef struct {
    char const * a[3] = {NULL, NULL, NULL};
} triple;

class GuidedSampler {
    std::string input_file;

    struct timespec start_time;
    double solver_time = 0.0;
    double check_time = 0.0;
    double cov_time = 0.0;
    double convert_time = 0.0;
    int max_samples;
    double max_time;

    z3::context c;
    int strategy;
    bool convert = false;
    bool use_predicates = false;
    bool use_random_predicates = false;
    bool get_internal_predicates = false;
    bool get_random_predicates = false;
    bool flip_preds = false;
    bool remove_repeated_classes = false;
    bool random_soft_preds = false;
    bool random_soft_bit = false;
    int common_bv_size = 1;
    z3::apply_result * res0;
    z3::goal * converted_goal;
    z3::params params;
    z3::optimize opt;
    z3::solver solver;
    z3::model model;
    z3::expr smt_formula;
    std::vector<z3::func_decl> variables;
    std::vector<z3::func_decl> ind;
    std::vector<z3::expr> constraints;
    std::vector<z3::expr> predicates;
    std::unordered_set<int> pred_list;
    std::unordered_map<int, std::vector<z3::expr>> preds_map;
    std::vector<std::pair<int,int>> cons_to_ind;
    std::unordered_map<int, std::unordered_set<int>> unsat_ind;
    std::unordered_set<int> unsat_internal;
    std::unordered_set<std::string> all_mutations;
    std::unordered_set<std::string> all_preds;
    int epochs = 0;
    int flips = 0;
    int samples = 0;
    int valid_samples = 0;
    int solver_calls = 0;
    int unsat_ind_count = 0;
    int all_ind_count = 0;

    std::ofstream results_file;

public:
    GuidedSampler(std::string input, int max_samples, double max_time, int strat, bool get_internal_predicates, bool get_random_predicates, bool use_predicates, bool use_random_predicates) :
               opt(c), params(c), solver(c), model(c), smt_formula(c), input_file(input), max_samples(max_samples), max_time(max_time), strategy(strat), get_internal_predicates(get_internal_predicates), get_random_predicates(get_random_predicates), use_predicates(use_predicates), use_random_predicates(use_random_predicates) {
        z3::set_param("rewriter.expand_select_store", "true");
        params.set("timeout", 10000u);
        opt.set(params);
        solver.set(params);
        convert = strategy == STRAT_SAT;
        if (strategy == STRAT_PRED_SOFT || strategy == STRAT_PRED_HARD) {
            use_predicates = true;
        }
        if (strategy == STRAT_FLIP_PREDS) {
            strategy = STRAT_SMTBIT;
            use_predicates = true;
            flip_preds = true;
        }
        if (strategy == STRAT_REMOVE_REPEATED) {
            strategy = STRAT_SMTBIT;
            use_predicates = true;
            flip_preds = true;
            remove_repeated_classes = true;
        }
        if (strategy == STRAT_RANDOM_SOFT_PREDS) {
            strategy = STRAT_SMTBIT;
            use_predicates = true;
            flip_preds = true;
            remove_repeated_classes = true;
            random_soft_preds = true;
        }
        if (get_internal_predicates) {
            get_coverage_vector = true;
        }
    }

    void run() {
        clock_gettime(CLOCK_REALTIME, &start_time);
        srand(start_time.tv_sec);
        // parse_cnf();
        parse_smt();
        results_file.open(input_file + ".samples");
        while (true) {
            opt.push();
            solver.push();
            if (random_soft_preds || strategy == STRAT_PRED_SOFT) {
                for (z3::expr & v : predicates) {
                    if (rand() % 2)
                        assert_soft(v);
                    else
                        assert_soft(!v);
                }
            }
            if (strategy == STRAT_PRED_SOFT) {
                z3::check_result result = solve();
                if (result == z3::sat) {
                    output(model, 0);
                    if (samples % 10 == 0)
                        print_stats();
                }

                opt.pop();
                solver.pop();

                continue;
            }
            if (strategy == STRAT_PRED_HARD) {
                for (z3::expr & v : predicates) {
                    if (rand() % 2)
                        solver.add(v);
                    else
                        solver.add(!v);
                }
                z3::check_result result = solve();
                if (result == z3::sat) {
                    output(model, 0);
                    if (samples % 10 == 0)
                        print_stats();
                }

                opt.pop();
                solver.pop();

                continue;
            }
            for (z3::func_decl & v : ind) {
                if (v.arity() > 0 || v.range().is_array())
                    continue;
                switch (v.range().sort_kind()) {
                case Z3_BV_SORT:
                {
		    if (random_soft_bit) {
                        for (int i = 0; i < v.range().bv_size(); ++i) {
                            if (rand() % 2)
                                assert_soft(v().extract(i, i) == c.bv_val(0, 1));
                            else
                                assert_soft(v().extract(i, i) != c.bv_val(0, 1));
                        }
		    } else {
                        std::string n;
                        char num[10];
                        int i = v.range().bv_size();
                        if (i % 4) {
                            snprintf(num, 10, "%x", rand() & ((1<<(i%4)) - 1));
                            n += num;
                            i -= (i % 4);
                        }
                        while (i) {
                            snprintf(num, 10, "%x", rand() & 15);
                            n += num;
                            i -= 4;
                        }
                        Z3_ast ast = parse_bv(n.c_str(), v.range(), c);
                        z3::expr exp(c, ast);
                        assert_soft(v() == exp);
		    }
                    break;
                }
                case Z3_BOOL_SORT:
                    if (rand() % 2)
                        assert_soft(v());
                    else
                        assert_soft(!v());
                    break;
                default:
                    std::cout << "Invalid sort\n";
                    exit(1);
                }

            }
            z3::check_result result = solve();
            if (result == z3::unsat) {
                std::cout << "No solutions\n";
                break;
            } else if (result == z3::unknown) {
                std::cout << "Could not solve\n";
                break;
            }

            opt.pop();
            solver.pop();

            sample(model);
        }
    }

    void assert_soft(z3::expr const & e) {
        opt.add(e, 1);
    }

    void print_stats() {
        struct timespec end;
        clock_gettime(CLOCK_REALTIME, &end);
        double elapsed = duration(&start_time, &end);
        std::cout << "Samples " << samples << '\n';
        std::cout << "Valid samples " << valid_samples << '\n';
        std::cout << "Unique valid samples " << all_mutations.size() << '\n';
        if (use_predicates)
            std::cout << "Unique predicates " << all_preds.size() << '\n';
        std::cout << "Total time " << elapsed << '\n';
        std::cout << "Solver time: " << solver_time << '\n';
        std::cout << "Convert time: " << convert_time << '\n';

        std::cout << "Check time " << check_time << '\n';
        std::cout << "Coverage time: " << cov_time << '\n';
        std::cout << "Coverage bool: " << coverage_bool - coverage_all_bool << '/' << coverage_all_bool << ", coverage bv " << coverage_bv - coverage_all_bv << '/' << coverage_all_bv << '\n';
        std::cout << "Epochs " << epochs << ", Flips " << flips << ", UnsatInd " << unsat_ind_count << '/' << all_ind_count << ", UnsatInternal " << unsat_internal.size() << ", Calls " << solver_calls << '\n' << std::flush;
    }

    std::unordered_set<Z3_ast> sub;
    std::unordered_set<Z3_ast> sup;
    std::unordered_set<std::string> var_names = {"bv", "true", "false"};
    int num_arrays = 0, num_bv = 0, num_bools = 0, num_bits = 0, num_uf = 0;
    int maxdepth = 0;

    void visit(z3::expr e, int depth = 0) {
        if (sup.find(e) != sup.end())
            return;
        assert(e.is_app());
        z3::func_decl fd = e.decl();
        if (e.is_const()) {
            std::string name = fd.name().str();
            if (var_names.find(name) == var_names.end()) {
                var_names.insert(name);
                // std::cout << "declaration: " << fd << '\n';
                variables.push_back(fd);
                if (fd.range().is_array()) {
                   ++num_arrays;
                } else if (fd.is_const()) {
                    switch (fd.range().sort_kind()) {
                    case Z3_BV_SORT:
                        ++num_bv;
                        num_bits += fd.range().bv_size();
                        break;
                    case Z3_BOOL_SORT:
                        ++num_bools;
                        ++num_bits;
                        break;
                    default:
                        std::cout << "Invalid sort\n";
                        exit(1);
                    }
                }
            }
        } else if (fd.decl_kind() == Z3_OP_UNINTERPRETED) {
            std::string name = fd.name().str();
            if (var_names.find(name) == var_names.end()) {
                var_names.insert(name);
                // std::cout << "declaration: " << fd << '\n';
                variables.push_back(fd);
                ++num_uf;
            }
        }
        sup.insert(e);
        if (depth > maxdepth)
            maxdepth = depth;
        for (int i = 0; i < e.num_args(); ++i)
            visit(e.arg(i), depth + 1);

        if (e.is_bool() || e.is_bv()) {
            sub.insert(e);
            coverage cov = {0};
            cov.index = coverage_vector.size();
            coverage_count cov_count = {0};
            coverage_vector.push_back(cov_count);
            covered.emplace(e, cov);
            if (use_predicates && !use_random_predicates && pred_list.find(cov.index) != pred_list.end()) {
                if (e.is_bool())
                    predicates.push_back(e);
                else
                    predicates.push_back(e.extract(0, 0) == c.bv_val(0, 1));
            }
        }
    }

    void parse_smt() {
        z3::expr formula = c.parse_file(input_file.c_str());
        Z3_ast ast = formula;
        if (ast == NULL) {
            std::cout << "Could not read input formula.\n";
            exit(1);
        }
        smt_formula = formula;
        if (convert) {
            z3::tactic simplify(c, "simplify");
            z3::tactic bvarray2uf(c, "bvarray2uf");
	    z3::tactic ackermannize_bv(c, "ackermannize_bv");
            z3::tactic bit_blast(c, "bit-blast");
            z3::tactic t = simplify & bvarray2uf & ackermannize_bv & bit_blast;
            z3::goal g(c);
            g.add(formula);

            struct timespec start;
            clock_gettime(CLOCK_REALTIME, &start);
	    z3::apply_result * res0 = new z3::apply_result(t(g));
            struct timespec end;
            clock_gettime(CLOCK_REALTIME, &end);
            convert_time += duration(&start, &end);

            assert(res0->size() == 1);
            converted_goal = new z3::goal((*res0)[0]);
            formula = converted_goal->as_expr();

            z3::solver s(c);
            s.set(params);
            s.add(formula);
            z3::check_result result = z3::unknown;
            try {
                result = s.check();
            } catch (z3::exception except) {
                std::cout << "Exception: " << except << "\n";
            }
            if (result == z3::unsat) {
                std::cout << "Formula is unsat\n";
                exit(0);
            } else if (result == z3::unknown) {
                std::cout << "Solver returned unknown\n";
                exit(0);
            }
            z3::model m = s.get_model();
            ind = get_variables(m, true);
            z3::model original = res0->convert_model(m);
            evaluate(original, smt_formula, true, 1);

            opt.add(formula);
            solver.add(formula);
        } else {
            opt.add(formula);
            solver.add(formula);
            z3::check_result result = solve();
            if (result == z3::unsat) {
                std::cout << "Formula is unsat\n";
                exit(0);
            } else if (result == z3::unknown) {
                std::cout << "Solver could not solve\n";
                exit(0);
            }
            evaluate(model, smt_formula, true, 1);
        }

        if (use_predicates && !use_random_predicates) {
            int p;
            std::ifstream f(input_file + ".internal");
            if (!f.is_open()) {
                std::cout << "No internal predicates file\n";
                exit(1);
            }
            while (f >> p)
                pred_list.insert(p);
            if (pred_list.size() == 0) {
                std::cout << "No internal predicates\n";
                exit(1);
            }
        }

        visit(smt_formula);
        if (use_predicates && use_random_predicates) {
            int i = 0;
            while (true) {
                std::string pred_file = input_file + ".pred" + std::to_string(i);
                std::ifstream file(pred_file);
                if (!file)
                    break;
                z3::expr pred = c.parse_file(pred_file.c_str());
                predicates.push_back(pred);
                ++i;
            }
        }
        std::cout << "Nodes " << sup.size() << '\n';
        std::cout << "Internal nodes " << sub.size() << '\n';
        std::cout << "Arrays " << num_arrays << '\n';
        std::cout << "Bit-vectors " << num_bv << '\n';
        std::cout << "Bools " << num_bools << '\n';
        std::cout << "Bits " << num_bits << '\n';
        std::cout << "Uninterpreted functions " << num_uf << '\n';
        if (!convert) {
            ind = variables;
        }
    }

    void generate_random_predicates() {
        common_bv_size = 1;
        int max_value = 0;
        for (auto & it : preds_map) {
            if (it.first && it.second.size() > max_value) {
                common_bv_size = it.first;
                max_value = it.second.size();
            }
        }
        int num = 16 + (rand() % 32);
        for(int i = 0; i < num; ++i) {
            std::ofstream pred_file(input_file + ".pred" + std::to_string(i));
            z3::solver s(c);
            s.add(generate_pred(1.0));
            pred_file << s.to_smt2();
            pred_file.close();
        }
    }

    z3::expr generate_pred(double p) {
        if (rand() <= p * RAND_MAX) {
            p -= 0.2;

            switch (rand() % 8) {
            case 0:
                return generate_pred(p) && generate_pred(p);
            case 1:
                return generate_pred(p) || generate_pred(p);
            case 2:
                return !generate_pred(p);
            case 3:
                return ult(generate_bv(p), generate_bv(p));
            case 4:
                return ule(generate_bv(p), generate_bv(p));
            case 5:
                return generate_bv(p) < generate_bv(p);
            case 6:
                return generate_bv(p) <= generate_bv(p);
            case 7:
                return generate_bv(p) == generate_bv(p);
            default:
                abort();
            }
        } else {
            int size = preds_map[0].size();
            int a = rand() % (size + 1);
            if (a == size)
                return c.bool_val(rand() % 2);
            else
                return preds_map[0][a];
        }
    }

    z3::expr generate_bv(double p) {
        if (rand() <= p * RAND_MAX) {
            p -= 0.2;

            switch (rand() % 15) {
            case 0:
                return ~generate_bv(p);
            case 1:
                return -generate_bv(p);
            case 2:
                return generate_bv(p) & generate_bv(p);
            case 3:
                return generate_bv(p) | generate_bv(p);
            case 4:
                return generate_bv(p) + generate_bv(p);
            case 5:
                return generate_bv(p) - generate_bv(p);
            case 6:
                return generate_bv(p) * generate_bv(p);
            case 7:
                return udiv(generate_bv(p), generate_bv(p));
            case 8:
                return urem(generate_bv(p), generate_bv(p));
            case 9:
                return generate_bv(p) / generate_bv(p);
            case 10:
                return srem(generate_bv(p), generate_bv(p));
            case 11:
                return smod(generate_bv(p), generate_bv(p));
            case 12:
                return shl(generate_bv(p), generate_bv(p));
            case 13:
                return lshr(generate_bv(p), generate_bv(p));
            case 14:
                return ashr(generate_bv(p), generate_bv(p));
            default:
                abort();
            }
        } else {
            int size = preds_map[common_bv_size].size();
            int a = rand() % (size + 1);
            if (a == size)
                return c.bv_val(0, common_bv_size);
            else
                return preds_map[common_bv_size][a];
        }
    }

    z3::expr evaluate(z3::model m, z3::expr e, bool b, int n) {
        coverage_enable = n;
        z3::expr res = m.eval(e, b);
        coverage_enable = 0;
        return res;
    }

    std::vector<z3::func_decl> get_variables(z3::model m, bool is_ind) {
        std::vector<z3::func_decl> ind;
        std::string str = "variable: ";
        if (is_ind) {
            str = "ind: ";
        }
        for (int i = 0; i < m.size(); ++i) {
            z3::func_decl fd = m[i];
            if (!is_ind && (fd.name().kind() == Z3_INT_SYMBOL || fd.name().str().find("k!") == 0)) {
                std::cout << fd << ": ignoring\n";
                continue;
            }
            ind.push_back(fd);
            std::cout << str << fd << '\n';
        }
        return ind;
    }

    void parse_cnf() {
        z3::expr_vector exp(c);
        std::ifstream f(input_file);
        assert(f.is_open());
        std::string line;
        while (getline(f, line)) {
            std::istringstream iss(line);
            if(line.find("c ind ") == 0) {
                std::string s;
                iss >> s;
                iss >> s;
                int v;
                while (!iss.eof()) {
                    iss >> v;
                    if (v)
                        ind.push_back(literal(v).decl());
                }
            } else if (line[0] != 'c' && line[0] != 'p') {
                z3::expr_vector clause(c);
                int v;
                while (!iss.eof()) {
                    iss >> v;
                    if (v > 0)
                        clause.push_back(literal(v));
                    else if (v < 0)
                        clause.push_back(!literal(-v));
                }
                exp.push_back(mk_or(clause));
            }
        }
        f.close();
        z3::expr formula = mk_and(exp);
        opt.add(formula);
        solver.add(formula);
    }

    z3::expr value(char const * n, z3::sort s) {
        switch (s.sort_kind()) {
        case Z3_BV_SORT:
        {
            Z3_ast ast = parse_bv(n, s, c);
            z3::expr exp(c, ast);
            return exp;
        }
        case Z3_BOOL_SORT:
            return c.bool_val(atoi(n) == 1);
        default:
            std::cout << "Invalid sort\n";
            exit(1);
        }
    }

    void sample(z3::model m) {
        std::unordered_set<std::string> mutations;
        std::unordered_set<std::string> classes;
        std::string m_string = model_string(m, ind);
        output(m, 0);
        opt.push();
        solver.push();
        size_t pos = 0;

        constraints.clear();
        cons_to_ind.clear();
        all_ind_count = 0;

        for (int count = 0; count < ind.size(); ++count) {
            z3::func_decl & v = ind[count];
            if (v.range().is_array()) {
                assert(m_string.c_str()[pos] == '[');
                ++pos;
                int num = atoi(m_string.c_str() + pos);
                pos = m_string.find('\0', pos) + 1;

                z3::expr def = value(m_string.c_str() + pos, v.range().array_range());
                pos = m_string.find('\0', pos) + 1;

                for (int j = 0; j < num; ++j) {
                    z3::expr arg = value(m_string.c_str() + pos, v.range().array_domain());
                    pos = m_string.find('\0', pos) + 1;
                    z3::expr val = value(m_string.c_str() + pos, v.range().array_range());
                    pos = m_string.find('\0', pos) + 1;

                    add_constraints(z3::select(v(), arg), val, -1);
                }
                assert(m_string.c_str()[pos] == ']');
                ++pos;
            } else if (v.is_const()) {
                z3::expr a = value(m_string.c_str() + pos, v.range());
                pos = m_string.find('\0', pos) + 1;
                add_constraints(v(), a, count);
            } else {
                assert(m_string.c_str()[pos] == '(');
                ++pos;
                int num = atoi(m_string.c_str() + pos);
                pos = m_string.find('\0', pos) + 1;

                z3::expr def = value(m_string.c_str() + pos, v.range());
                pos = m_string.find('\0', pos) + 1;

                for (int j = 0; j < num; ++j) {
                    z3::expr_vector args(c);
                    for (int k = 0; k < v.arity(); ++k) {
                        z3::expr arg = value(m_string.c_str() + pos, v.domain(k));
                        pos = m_string.find('\0', pos) + 1;
                        args.push_back(arg);
                    }
                    z3::expr val = value(m_string.c_str() + pos, v.range());
                    pos = m_string.find('\0', pos) + 1;

                    add_constraints(v(args), val, -1);
                }
                assert(m_string.c_str()[pos] == ')');
                ++pos;
            }
        }

        if (get_random_predicates) {
            generate_random_predicates();
            exit(0);
        }

        if (use_predicates && flip_preds) {
            constraints.clear();
            cons_to_ind.clear();
            for (z3::expr & v : predicates) {
                z3::expr b = m.eval(v, true);
                cons_to_ind.emplace_back(-1, -1);
                constraints.push_back(v == b);
                assert_soft(v == b);
            }
        }

        struct timespec etime;
        clock_gettime(CLOCK_REALTIME, &etime);
        double start_epoch = duration(&start_time, &etime);

        print_stats();
        int calls = 0;
        int progress = 0;
        for (int count = 0; count < constraints.size(); ++count) {
            auto u = unsat_ind.find(cons_to_ind[count].first);
            if (u != unsat_ind.end() && u->second.find(cons_to_ind[count].second) != u->second.end()) {
                continue;
            }
            z3::expr & cond = constraints[count];
            opt.push();
            solver.push();
            opt.add(!cond);
            solver.add(!cond);

            struct timespec end;
            clock_gettime(CLOCK_REALTIME, &end);
            double elapsed = duration(&start_time, &end);

            double cost = calls ? (elapsed - start_epoch) / calls : 0.0;
            cost *= constraints.size() - count;
            if (max_time/3.0 + start_epoch > max_time && elapsed + cost > max_time) {
                std::cout << "Stopping: slow\n";
                finish();
            }
            z3::check_result result = z3::unknown;
            if (cost * rand() <= (max_time/3.0 + start_epoch - elapsed) * RAND_MAX) {
                result = solve();
                ++calls;
            }
            if (result == z3::sat) {
                std::string new_string = model_string(model, ind);
                if (mutations.find(new_string) == mutations.end()) {
                    std::string pred_string;
                    if (remove_repeated_classes)
                        pred_string = get_preds(model);
                    if (classes.find(pred_string) == classes.end()) {
                        mutations.insert(new_string);
                        if (remove_repeated_classes)
                            classes.insert(pred_string);
                        output(model, 1);
                        flips += 1;
                    }
                } else {
                    // std::cout << "repeated\n";
                }
            } else if (result == z3::unsat) {
                // std::cout << "unsat\n";
                if (use_predicates && flip_preds) {
                    unsat_internal.insert(count);
                }
                if (cons_to_ind[count].first >= 0) {
                    unsat_ind[cons_to_ind[count].first].insert(cons_to_ind[count].second);
                    ++unsat_ind_count;
                }
            }
            opt.pop();
            solver.pop();
            double new_progress = 80.0 * (double)(count + 1) / (double)constraints.size();
            while (progress < new_progress) {
                ++progress;
                std::cout << '=' << std::flush;
            }
        }
        std::cout << '\n';

        std::vector<std::string> initial(mutations.begin(), mutations.end());
        std::vector<std::string> sigma = initial;

        for (int k = 2; k <= 6; ++k) {
                std::cout << "Combining " << k << " mutations\n";
                std::vector<std::string> new_sigma;
                int all = 0;
                int good = 0;

                for (std::string b_string : sigma) {
                    for (std::string c_string : initial) {
                        size_t pos_a = 0;
                        size_t pos_b = 0;
                        size_t pos_c = 0;
                        std::string candidate;
                        for (z3::func_decl & w : ind) {
                            if (w.range().is_array()) {
                                int arity = 0;
                                z3::sort s = w.range().array_range();
                                combine_function(m_string, b_string, c_string,
                                                 pos_a, pos_b, pos_c, arity, s, candidate);
                            } else if (w.is_const()) {
                                z3::sort s = w.range();
				std::cout << "m_string\n" << m_string << "\nb_string\n" << b_string << "\nc_string\n" << c_string << "\n";
                                std::string num = combine(m_string.c_str() + pos_a, b_string.c_str() + pos_b, c_string.c_str() + pos_c, s);
                                pos_a = m_string.find('\0', pos_a) + 1;
                                pos_b = b_string.find('\0', pos_b) + 1;
                                pos_c = c_string.find('\0', pos_c) + 1;
                                candidate += num + '\0';
                            } else {
                                int arity = w.arity();
                                z3::sort s = w.range();
                                combine_function(m_string, b_string, c_string,
                                                 pos_a, pos_b, pos_c, arity, s, candidate);
                            }
                        }
                        if (false) {
			    z3::model b_model = gen_model(b_string, variables);
                            z3::model c_model = gen_model(c_string, variables);
                            z3::model cand_model = gen_model(candidate, variables);
                            std::string pred_a = get_preds(m);
                            std::string pred_b = get_preds(b_model);
                            std::string pred_c = get_preds(c_model);
                            std::string pred_cand = get_preds(cand_model);
                            for (int i = 0; i < predicates.size(); ++i) {
                                bool a = pred_a[i] == '1';
                                bool b = pred_b[i] == '1';
                                bool c = pred_c[i] == '1';
                                bool cand = pred_cand[i] == '1';
                                int good = a ^ ((a ^ b) | (a ^ c)) == cand;
                                std::cout << good;
                            }
                            std::cout << '\n';
                        }
                        if (mutations.find(candidate) == mutations.end()) {
                            mutations.insert(candidate);
                            std::string pred_string;
                            z3::model cand_model(c);
                            if (!convert) {
                                cand_model = gen_model(candidate, variables);
                            }
                            if (remove_repeated_classes) {
                                pred_string = get_preds(cand_model);
                            }
                            if (classes.find(pred_string) == classes.end()) {
                                bool valid;
                                if (convert) {
                                    z3::model cand = gen_model(candidate, ind);
                                    valid = output(cand, k);
                                } else {
                                    valid = output(candidate, cand_model, k);
                                }
                                ++all;
                                if (valid) {
                                    ++good;
                                    new_sigma.push_back(candidate);
                                    if (remove_repeated_classes)
                                        classes.insert(pred_string);
                                }
                            }
                        }
                    }
                }
                double accuracy = (double)good / (double)all;
                std::cout << "Valid: " << good << " / " << all << " = " << accuracy << '\n';
                print_stats();
                if (all == 0 || accuracy < 0.1)
                    break;
                sigma = new_sigma;
        }

        epochs += 1;
        opt.pop();
        solver.pop();
    }

    void add_constraints(z3::expr exp, z3::expr val, int count) {
        switch (val.get_sort().sort_kind()) {
        case Z3_BV_SORT:
        {
            int size = val.get_sort().bv_size();
            if (get_random_predicates) {
                preds_map[size].push_back(exp);
            }
            for (int i = 0; i < size; ++i) {
                all_ind_count += (count >= 0);
                cons_to_ind.emplace_back(count, i);

                z3::expr r = val.extract(i, i);
                r = r.simplify();
                constraints.push_back(exp.extract(i, i) == r);
                if (strategy == STRAT_SMTBIT)
                    assert_soft(exp.extract(i, i) == r);
            }
            if (strategy == STRAT_SMTBV)
                assert_soft(exp == val);
            break;
        }
        case Z3_BOOL_SORT:
        {
            if (get_random_predicates) {
                preds_map[0].push_back(exp);
            }
            all_ind_count += (count >= 0);
            cons_to_ind.emplace_back(count, 0);
            constraints.push_back(exp == val);
            assert_soft(exp == val);
            break;
        }
        default:
            std::cout << "Invalid sort\n";
            exit(1);
        }
    }

    char const * parse_function(std::string const & m_string, size_t & pos, int arity, std::unordered_map<std::string,triple> & values, int index) {
        bool is_array = false;
        if (arity == 0) {
            is_array = true;
            arity = 1;
        }
        assert(m_string.c_str()[pos] == is_array? '[' : '(');
        ++pos;
        int num = atoi(m_string.c_str() + pos);
        pos = m_string.find('\0', pos) + 1;

        char const * def = m_string.c_str() + pos;
        pos = m_string.find('\0', pos) + 1;

        for (int j = 0; j < num; ++j) {
            int start = pos;
            for (int k = 0; k < arity; ++k) {
                pos = m_string.find('\0', pos) + 1;
            }
            std::string args = m_string.substr(start, pos - start);
            values[args].a[index] = m_string.c_str() + pos;
            pos = m_string.find('\0', pos) + 1;
        }
        assert(m_string.c_str()[pos] == is_array ? ']' : ')');
        ++pos;
        return def;
    }

    unsigned char hex(char c) {
        if ('0' <= c && c <= '9')
            return c - '0';
        else if ('a' <= c && c <= 'f')
            return 10 + c - 'a';
        std::cout << "Invalid hex\n";
        finish();
    }

    std::string combine(char const * val_a, char const * val_b, char const * val_c, z3::sort s) {
        std::string num;
        while (*val_a) {
            unsigned char a = hex(*val_a);
            unsigned char b = hex(*val_b);
            unsigned char c = hex(*val_c);
            unsigned char r = a ^ ((a ^ b) | (a ^ c));
            char n;
            if (r <= 9)
                n = '0' + r;
            else
                n = 'a' + r - 10;
            num += n;
            ++val_a;
            ++val_b;
            ++val_c;
        }
        return num;
    }

    void combine_function(std::string const & str_a, std::string const & str_b, std::string const & str_c,
                          size_t & pos_a, size_t & pos_b, size_t & pos_c, int arity, z3::sort s, std::string & candidate) {

        std::unordered_map<std::string,triple> values;
        char const * def_a = parse_function(str_a, pos_a, arity, values, 0);
        char const * def_b = parse_function(str_b, pos_b, arity, values, 1);
        char const * def_c = parse_function(str_c, pos_c, arity, values, 2);

        candidate += arity == 0 ? "[" : "(";
        candidate += std::to_string(values.size()) + '\0';
        std::string def = combine(def_a, def_b, def_c, s);
        candidate += def + '\0';
        for (auto value : values) {
            char const * val_a = value.second.a[0];
            if (!val_a)
                val_a = def_a;
            char const * val_b = value.second.a[1];
            if (!val_b)
                val_b = def_b;
            char const * val_c = value.second.a[2];
            if (!val_c)
                val_c = def_c;
            std::string val = combine(val_a, val_b, val_c, s);
            candidate += value.first;
            candidate += val + '\0';
        }
        candidate += arity == 0 ? "]" : ")";
    }

    z3::model gen_model(std::string candidate, std::vector<z3::func_decl> ind) {
        z3::model m(c);
        size_t pos = 0;
        for (z3::func_decl & v : ind) {
            if (v.range().is_array()) {
                assert(candidate.c_str()[pos] == '[');
                ++pos;
                int num = atoi(candidate.c_str() + pos);
                pos = candidate.find('\0', pos) + 1;

                z3::expr def = value(candidate.c_str() + pos, v.range().array_range());
                pos = candidate.find('\0', pos) + 1;

                Z3_sort domain_sort[1] = { v.range().array_domain() };
                Z3_sort range_sort = v.range().array_range();
                Z3_func_decl decl = Z3_mk_fresh_func_decl(c, "k", 1, domain_sort, range_sort);
                z3::func_decl fd(c, decl);

                z3::func_interp f = m.add_func_interp(fd, def);

                for (int j = 0; j < num; ++j) {
                    z3::expr arg = value(candidate.c_str() + pos, v.range().array_domain());
                    pos = candidate.find('\0', pos) + 1;
                    z3::expr val = value(candidate.c_str() + pos, v.range().array_range());
                    pos = candidate.find('\0', pos) + 1;

                    z3::expr_vector args(c);
                    args.push_back(arg);
                    f.add_entry(args, val);
                }
                z3::expr array = as_array(fd);
                m.add_const_interp(v, array);
                assert(candidate.c_str()[pos] == ']');
                ++pos;
            } else if (v.is_const()) {
                z3::expr a = value(candidate.c_str() + pos, v.range());
                pos = candidate.find('\0', pos) + 1;

                m.add_const_interp(v, a);
            } else {
                assert(candidate.c_str()[pos] == '(');
                ++pos;
                int num = atoi(candidate.c_str() + pos);
                pos = candidate.find('\0', pos) + 1;

                z3::expr def = value(candidate.c_str() + pos, v.range());
                pos = candidate.find('\0', pos) + 1;

                z3::func_interp f = m.add_func_interp(v, def);

                for (int j = 0; j < num; ++j) {
                    z3::expr_vector args(c);
                    for (int k = 0; k < v.arity(); ++k) {
                        z3::expr arg = value(candidate.c_str() + pos, v.domain(k));
                        pos = candidate.find('\0', pos) + 1;
                        args.push_back(arg);
                    }
                    z3::expr val = value(candidate.c_str() + pos, v.range());
                    pos = candidate.find('\0', pos) + 1;

                    f.add_entry(args, val);
                }
                assert(candidate.c_str()[pos] == ')');
                ++pos;
            }
        }
        return m;
    }

    bool output(z3::model m, int nmut) {
        std::string sample;
        z3::model model = m;
        if (convert) {
            struct timespec start, end;
            clock_gettime(CLOCK_REALTIME, &start);
            model = res0->convert_model(m);
            sample = model_string(model, variables);
            clock_gettime(CLOCK_REALTIME, &end);
            convert_time += duration(&start, &end);
        } else {
            sample = model_string(m, ind);
        }
        return output(sample, model, nmut);
    }

    bool output(std::string sample, z3::model m, int nmut) {
        samples += 1;

        struct timespec start, middle;
        clock_gettime(CLOCK_REALTIME, &start);

        double elapsed = duration(&start_time, &start);
        if (elapsed >= max_time) {
            std::cout << "Stopping: timeout\n";
            finish();
        }

        z3::expr b = evaluate(m, smt_formula, true, 0);

        bool valid = b.bool_value() == Z3_L_TRUE;
        if (valid) {
	    auto res = all_mutations.insert(sample);
	    if (res.second) {
                results_file << nmut << ": " << sample << '\n';
                if (use_predicates) {
                    std::string pred_string = get_preds(m);
                    all_preds.insert(pred_string);
                    results_file << "P: " << pred_string << '\n';
                }
	    }
	    ++valid_samples;
            clock_gettime(CLOCK_REALTIME, &middle);
	    evaluate(m, smt_formula, true, 2);
	} else if (nmut <= 1) {
	    std::cout << "Solution check failed, nmut = " << nmut << "\n";
	    std::cout << b << "\n";
	    exit(0);
	}

        struct timespec end;
        clock_gettime(CLOCK_REALTIME, &end);
        if (valid) {
            cov_time += duration(&middle, &end);
            check_time += duration(&start, &middle);
        } else {
            check_time += duration(&start, &end);
        }
        return valid;
    }

    std::string get_preds(z3::model m) {
        std::string s;
        for (z3::expr & v : predicates) {
            z3::expr b = m.eval(v, true);
            s += std::to_string(b.bool_value() == Z3_L_TRUE);
        }
        return s;
    }

    [[ noreturn ]] void finish() {
        print_stats();
        if (get_internal_predicates) {
            int d = 0;
            std::cout << "START\n";
            for (auto cov : coverage_vector) {
                if (cov.c0 && cov.c1)
                    std::cout << cov.c0 << " " << cov.c1 << " " << d << '\n';
                ++d;
            }
            std::cout << "END\n";
            std::ofstream internal(input_file + ".internal");
            std::unordered_set<std::pair<int, int>, pair_hash> hist;
            for (Z3_ast e : sub) {
                int index = covered[e].index;
                coverage_count count = coverage_vector[index];
                std::pair<int, int> p;
                if (count.c0 < count.c1) {
                    p.first = count.c1;
                    p.second = count.c0;
                } else {
                    p.first = count.c0;
                    p.second = count.c1;
                }
                if (p.second > 0 && hist.insert(p).second)
                    internal << index << '\n';
            }
            internal.close();
        }
        results_file.close();
        exit(0);
    }

    z3::check_result solve() {
        struct timespec start;
        clock_gettime(CLOCK_REALTIME, &start);
        double elapsed = duration(&start_time, &start);
        if (valid_samples >= max_samples) {
            std::cout << "Stopping: samples\n";
            finish();
        }
        if (elapsed >= max_time) {
            std::cout << "Stopping: timeout\n";
            finish();
        }
        z3::check_result result = z3::unknown;
        try {
            if (strategy != STRAT_PRED_HARD)
                result = opt.check();
        } catch (z3::exception except) {
            std::cout << "Exception: " << except << "\n";
        }
        if (result == z3::sat) {
            model = opt.get_model();
        } else if (result == z3::unknown && strategy != STRAT_PRED_SOFT) {
            try {
                result = solver.check();
            } catch (z3::exception except) {
                std::cout << "Exception: " << except << "\n";
            }
            if (result == z3::sat) {
                std::cout << 'S';
                model = solver.get_model();
            } else if (result == z3::unknown) {
                std::cout << 'T';
            } else if (strategy != STRAT_PRED_HARD) {
                std::cout << 'U';
            }
        }
        struct timespec end;
        clock_gettime(CLOCK_REALTIME, &end);
        solver_time += duration(&start, &end);
        solver_calls += 1;

        return result;
    }

    std::string model_string(z3::model m, std::vector<z3::func_decl> ind) {
        std::string s;
        for (z3::func_decl & v : ind) {
            if (v.range().is_array()) {
                z3::expr e = m.get_const_interp(v);
                Z3_func_decl as_array = Z3_get_as_array_func_decl(c, e);
                if (as_array) {
		    z3::func_interp f = m.get_func_interp(to_func_decl(c, as_array));
		    std::string num = "[";
		    num += std::to_string(f.num_entries());
		    s += num + '\0';
		    std::string def = bv_string(f.else_value(), c);
		    s += def + '\0';
		    for (int j = 0; j < f.num_entries(); ++j) {
		        std::string arg = bv_string(f.entry(j).arg(0), c);
		        std::string val = bv_string(f.entry(j).value(), c);
		        s += arg + '\0';
		        s += val + '\0';
		    }
		    s += "]";
                } else {
                    std::vector<std::string> args;
                    std::vector<std::string> values;
                    while (e.decl().name().str() == "store") {
                        std::string arg = bv_string(e.arg(1), c);
                        if (std::find(args.begin(), args.end(), arg) != args.end())
                            continue;
                        args.push_back(arg);
                        values.push_back(bv_string(e.arg(2), c));
                        e = e.arg(0);
                    }
		    std::string num = "[";
		    num += std::to_string(args.size());
		    s += num + '\0';
		    std::string def = bv_string(e.arg(0), c);
		    s += def + '\0';
		    for (int j = args.size() - 1; j >= 0; --j) {
		        std::string arg = args[j];
		        std::string val = values[j];
		        s += arg + '\0';
		        s += val + '\0';
		    }
		    s += "]";
                }
            } else if (v.is_const()) {
                z3::expr b = m.get_const_interp(v);
                Z3_ast ast = b;
                switch (v.range().sort_kind()) {
                case Z3_BV_SORT:
                {
                    if (!ast) {
                        s += bv_string(c.bv_val(0, v.range().bv_size()), c) + '\0';
                    } else {
                        s += bv_string(b, c) + '\0';
		    }
                    break;
                }
                case Z3_BOOL_SORT:
		{
                    if (!ast) {
                        s += std::to_string(false) + '\0';
                    } else {
                        s += std::to_string(b.bool_value() == Z3_L_TRUE) + '\0';
		    }
                    break;
		}
                default:
                        std::cout << "Invalid sort\n";
                        exit(1);
                }
            } else {
                z3::func_interp f = m.get_func_interp(v);
                std::string num = "(";
                num += std::to_string(f.num_entries());
                s += num + '\0';
                std::string def = bv_string(f.else_value(), c);
                s += def + '\0';
                for (int j = 0; j < f.num_entries(); ++j) {
                    for (int k = 0; k < f.entry(j).num_args(); ++k) {
                        std::string arg = bv_string(f.entry(j).arg(k), c);
                        s += arg + '\0';
                    }
                    std::string val = bv_string(f.entry(j).value(), c);
                    s += val + '\0';
                }
                s += ")";
            }
        }
        return s;
    }

    double duration(struct timespec * a, struct timespec * b) {
        return (b->tv_sec - a->tv_sec) + 1.0e-9 * (b->tv_nsec - a->tv_nsec);
    }

    z3::expr literal(int v) {
        return c.constant(c.str_symbol(std::to_string(v).c_str()), c.bool_sort());
    }
};

int main(int argc, char * argv[]) {
    int max_samples = 1000000;
    double max_time = 3600.0;
    int strategy = STRAT_SMTBIT;
    if (argc < 2) {
        std::cout << "Argument required: input file\n";
        return 0;
    }
    bool get_internal_predicates = false;
    bool get_random_predicates = false;
    bool use_predicates = false;
    bool use_random_predicates = false;
    bool arg_samples = false;
    bool arg_time = false;
    for (int i = 1; i < argc - 1; ++i) {
        if (strcmp(argv[i], "-n") == 0)
            arg_samples = true;
        else if (strcmp(argv[i], "-t") == 0)
            arg_time = true;
        else if (strcmp(argv[i], "--smtbit") == 0)
            strategy = STRAT_SMTBIT;
        else if (strcmp(argv[i], "--smtbv") == 0)
            strategy = STRAT_SMTBV;
        else if (strcmp(argv[i], "--sat") == 0)
            strategy = STRAT_SAT;
        else if (strcmp(argv[i], "--pred-hard") == 0)
            strategy = STRAT_PRED_HARD;
        else if (strcmp(argv[i], "--pred-soft") == 0)
            strategy = STRAT_PRED_SOFT;
        else if (strcmp(argv[i], "--flip-preds") == 0)
            strategy = STRAT_FLIP_PREDS;
        else if (strcmp(argv[i], "--remove-repeated") == 0)
            strategy = STRAT_REMOVE_REPEATED;
        else if (strcmp(argv[i], "--random-soft-preds") == 0)
            strategy = STRAT_RANDOM_SOFT_PREDS;
        else if (strcmp(argv[i], "--get-internal-predicates") == 0)
            get_internal_predicates = true;
        else if (strcmp(argv[i], "--get-random-predicates") == 0)
            get_random_predicates = true;
        else if (strcmp(argv[i], "--use-internal-predicates") == 0)
            use_predicates = true;
        else if (strcmp(argv[i], "--use-random-predicates") == 0) {
            use_predicates = true;
            use_random_predicates = true;
        } else if (arg_samples) {
            arg_samples = false;
            max_samples = atoi(argv[i]);
        } else if (arg_time) {
            arg_time = false;
            max_time = atof(argv[i]);
        } else {
            std::cout << "Invalid argument\n";
            exit(1);
        }
    }
    GuidedSampler s(argv[argc-1], max_samples, max_time, strategy, get_internal_predicates, get_random_predicates,
                 use_predicates, use_random_predicates);
    try {
        s.run();
    } catch (z3::exception except) {
        std::cout << "z3 exception:" << except << '\n';
        s.finish();
    } catch (std::bad_alloc except) {
        std::cout << "bad_alloc exception" << '\n';
        s.finish();
    } catch (...) {
        std::cout << "unknown exception" << '\n';
        s.finish();
    }
    return 0;
}
