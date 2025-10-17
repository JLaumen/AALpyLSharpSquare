from algorithm import learn
from fa_learner import FALearner
from dfa3_encoder import DFA3Encoder
from rpni_learner import RPNILearner
from aalpy.utils import make_input_complete, load_automaton_from_file
from rc_lstar import run_Lstar
import time
from system_dc_sul_s_t import SystemDCSULST
from system_dc_oracle_s_t import SystemDCOracleST
from complete_dfa_oracle import CompleteDFAOracle
from copy import deepcopy
from aalpy.base.SUL import CacheSUL
from rers_sul_s_t import RERSSULST
from data.counter_examples import counter_examples_dict
from multiprocessing import Process, Queue
import random
from aalpy.learning_algs.deterministic.LSharpSquare import run_lsharp_square


def run(example, t_type):
    # T2 update
    M = load_automaton_from_file(f'data/{example}/T{t_type}.dot', automaton_type='dfa') #
    make_input_complete(M, missing_transition_go_to="sink_state")

    # # T2 update
    # from symbolic_dfa_t2 import SymbolicDFAT2
    # M = SymbolicDFAT2(counter_examples_dict[example][t_type][0][1])

    system_sul = CacheSUL(
        RERSSULST(benchmark=example, t_type=t_type, for_T=False, is_prefix_closed=False, is_suffix_closed=False))
    alphabet = system_sul.sul.alphabet
    sul = SystemDCSULST(M, system_sul)
    # print(B.execute_sequence(B.initial_state, ('C', 'C', 'B', 'D', 'C', 'C', 'C', 'B', 'D', 'C', 'B', 'D')))
    oracle = SystemDCOracleST(alphabet, sul, M, counter_examples_dict[example][t_type], walks_per_state=300,
                              walk_len=30, example=example, t_type=t_type)

    # dfa3, data = run_Lstar(alphabet,
    #                        sul,
    #                        oracle,
    #                        closing_strategy='longest_first',
    #                        cex_processing=None,
    #                        automaton_type='moore',
    #                        cache_and_non_det_check=False,
    #                        return_data=True,
    #                        print_level=0)
    dfa3, data = run_lsharp_square(alphabet,
                                   sul,
                                   oracle,
                                   return_data=True)

    data["ce_length"] = len(counter_examples_dict[example][t_type][0][1])
    data["alphabet_size"] = len(alphabet)
    data["T_size"] = len(M.states)
    data["B_size"] = 0
    data["system_steps"] = system_sul.sul.system_steps
    data["system_inits"] = system_sul.sul.system_inits
    data["system_steps_knowing_s"] = system_sul.sul.system_steps_knowing_s
    data["system_inits_knowing_s"] = system_sul.sul.system_inits_knowing_s
    return dfa3, data, M, []



def main_single(benchmark, t_type, method, description_type, early_detection):
    random.seed(0)
    example = benchmark  # "m183"  # "magento", "threads_example", "coffee", "coffee_new", "api_alice", "api_bob", "peterson", "m183"

    start_time = time.time()
    dfa3, data, M, B = run(example, t_type)
    end_time = time.time()
    # print(len(dfa3.states))
    # print(dfa3)
    results = {"benchmark": benchmark}
    results["3DFA"] = data["automaton_size"]

    if t_type == "1":
        # results = { col_name:results[col_name] for col_name in ["benchmark", "ce_length", "alphabet_size", "3DFA", "L* time", "FE_DFA", "B_size"]}
        results = {col_name: results[col_name] for col_name in ["benchmark", "3DFA", "L* time"]}
    elif t_type == "2":
        results = { col_name:results[col_name] for col_name in ["benchmark", "ce_length", "alphabet_size", "T_size", "3DFA", "L* time", "FE_DFA", "FE_ED_DFA", "B_size"]}
    else:
        results = {col_name: results[col_name] for col_name in ["benchmark", "ce_length", "alphabet_size", "3DFA", "L* time", "FE_DFA", "RC_DFA", "B_size"]}

    return results
