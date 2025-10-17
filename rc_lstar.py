from aalpy.oracles import BreadthFirstExplorationEqOracle, RandomWalkEqOracle, RandomWMethodEqOracle
from bfe_oracle import BFEOracle
from dc_lstar import run_Lstar
from rc_sul import RCSUL
from rc_oracle import RCOracle, SampleBasedRCOracle
from aalpy.automata.Dfa import Dfa
from aalpy.automata.MealyMachine import MealyMachine
from dc_dfa import find_minimal_consistent_dfa
from aalpy.learning_algs.deterministic.ObservationTable import ObservationTable
import time
from aalpy.utils import load_automaton_from_file, save_automaton_to_file, make_input_complete
from aalpy.base.Oracle import Oracle
from aalpy.automata.MooreMachine import MooreMachine
from random import randint, choice, sample, random, shuffle
from aalpy.learning_algs import run_RPNI
from dfa_equivalence import sample_based_dfa_equivalence, get_dfas_distance
from utils import get_intersection_dfa
from collections import Counter


def observation_table_to_data(observation_table: ObservationTable, is_system_prefix_closed=True):
    data = []
    for prefix in observation_table.T:
        labels = observation_table.T[prefix]
        for i, label in enumerate(labels):
            if label == "?":
                continue
            data.append((prefix + observation_table.E[i], label == "+"))
            if is_system_prefix_closed:
                if label == "-":
                    w = prefix + observation_table.E[i]
                    for j in range(len(w)):
                        data.append((w[:j], False))
    return data


def dfa3_to_data(dfa3: MooreMachine):
    from itertools import product
    data = []
    data.append((tuple(), False))  # empty word is not a bug
    for i in range(1, 8):
        for l in product(dfa3.get_input_alphabet(), repeat=i):
            result = dfa3.execute_sequence(dfa3.initial_state, l)
            if result[-1] != "?":
                data.append((l, result[-1] == "+"))
    return data


def generate_tests(M, B, num_tests, cut_prob, method="random_walk"):
    if method == "random_walk":
        failed_tests, passed_tests = set(), set()
        seq = []
        while len(failed_tests) + len(passed_tests) < num_tests or len(failed_tests) == 0 or len(passed_tests) == 0:
            available_transitions = M.current_state.get_diff_state_transitions() + M.current_state.get_same_state_transitions()
            if len(available_transitions) == 0 or (len(seq) > 0 and random() < cut_prob):
                if B.execute_sequence(B.initial_state, seq)[-1]:
                    failed_tests.add(tuple(seq))
                else:
                    passed_tests.add(tuple(seq))
                M.reset_to_initial()
                B.reset_to_initial()
                seq = []
            else:
                c = choice(available_transitions)
                M.step(c)
                seq.append(c)

        return failed_tests, passed_tests
    else:
        return method(M, B, num_tests)


def run_single_test(M, B, oracle_opt, test_set_size, name, dfa_generator_opt, test_generator_opt="random_walk", is_system_prefix_closed=True):
    results = {}
    # failed_tests, passed_tests = generate_tests(M, B, 1000, 0.2)
    # results["fail_prob"] = len(failed_tests) / (len(failed_tests) + len(passed_tests))
    failed_tests, passed_tests = generate_tests(M, B, test_set_size, 0.2, method=test_generator_opt)
    make_input_complete(M, 'sink_state')
    sul = RCSUL(M, B, failed_tests=failed_tests, passed_tests=passed_tests)
    if oracle_opt == "SampleBasedRCOracle":
        oracle = RCOracle(M.get_input_alphabet(), sul, SampleBasedRCOracle(M.get_input_alphabet(), sul, sample_size=10000))
    elif oracle_opt == "RandomWalkEqOracle":
        oracle = RCOracle(M.get_input_alphabet(), sul, RandomWalkEqOracle(M.get_input_alphabet(), sul, num_steps=10000))
    else:
        oracle = RCOracle(M.get_input_alphabet(), sul, RandomWMethodEqOracle(M.get_input_alphabet(), sul))

    dfa3, data = run_Lstar(M.get_input_alphabet(), sul, oracle, closing_strategy='longest_first', cex_processing=None,
                           automaton_type='moore', cache_and_non_det_check=False, return_data=True, print_level=0)

    results["dfa3_size"] = dfa3.size
    results["system_queries"] = data["system_queries"]
    results["l_star_time"] = data["total_time"]
    results["membership_queries"] = data["membership_queries"]
    results["equivalence_queries"] = data["equivalence_queries"]
    save_automaton_to_file(dfa3, path="output/" + name + "_dfa3")

    if dfa_generator_opt == 1:
        dfa_creation_start = time.time()
        # rpni_data = dfa3_to_data(dfa3)
        rpni_data = observation_table_to_data(data["observation_table"], is_system_prefix_closed=is_system_prefix_closed)
        import pickle
        with open("output/" + name + "_rpni_data", "wb") as f:
            pickle.dump(rpni_data, f)
        dfa = run_RPNI(rpni_data, automaton_type="dfa", print_info=False)
        dfa_creation_time = time.time() - dfa_creation_start
    else:
        dfa_creation_start = time.time()
        dfa, mealy_a = find_minimal_consistent_dfa(dfa3)
        save_automaton_to_file(mealy_a, path="output/" + name + "_mealy_a")
        dfa_creation_time = time.time() - dfa_creation_start


    # opt_a_start = time.time()
    # dfa, mealy_a = find_minimal_consistent_dfa(dfa3)
    # opt_a_time = time.time() - opt_a_start
    # results["dfa_time"] = opt_a_time
    # results["dfa_size"] = dfa.size
    # save_automaton_to_file(dfa, path="output/" + example + "_dfa_a")
    # save_automaton_to_file(mealy_a, path="output/" + example + "_mealy_a")
    # make_input_complete(dfa, 'sink_state')

    # print("option b:")


    save_automaton_to_file(dfa, path="output/" + name + "_dfa_b")
    results["dfa_time"] = dfa_creation_time
    results["dfa_size"] = dfa.size
    make_input_complete(dfa, 'sink_state')
    results["sample_based_similarity"] = sample_based_dfa_equivalence(M, dfa, B)
    #results["language_distance"] = get_dfas_distance(get_intersection_dfa(B, M), get_intersection_dfa(dfa, M))
    return results



