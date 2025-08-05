import time

from aalpy.base import Oracle, SUL
from aalpy.SULs import DfaSUL
from aalpy.utils.HelperFunctions import print_learning_info
from .ObservationTreeSquare import ObservationTreeSquare
from ...base.SUL import CacheSUL


def run_LsharpSquare(alphabet: list, sul: SUL, eq_oracle: Oracle, automaton_type,
                     samples=None,
                     max_learning_rounds=None, cache_and_non_det_check=True, return_data=False, print_level=2):
    """
    Based on ''A New Approach for Active Automata Learning Based on Apartness'' from Vaandrager, Garhewal, Rot and Wissmann. 
    and ''L# for DFAs'' from Vaandrager, Sanders.

    The algorithm learns a DFA/Moore machine/Mealy machine using apartness and an observation tree. 

    Args:

        alphabet: input alphabet

        sul: system under learning

        eq_oracle: equivalence oracle

        automaton_type: type of automaton to be learned. Either 'dfa', 'mealy' or 'moore'

        extension_rule: strategy used during the extension rule. Options: None, "SepSeq" (default) and "ADS".

        separation_rule: strategy used during the extension rule. Options: "SepSeq" (default) and "ADS".

        samples: input output traces provided to the learning algorithm. They are added to cache and could reduce
        total interaction with the system. Syntax: list of [(input_sequence, output_sequence)] or None

        max_learning_rounds: number of learning rounds after which learning will terminate (Default value = None)

        cache_and_non_det_check: Use caching and non-determinism checks (Default value = True)

        return_data: if True, a map containing all information(runtime/#queries/#steps) will be returned
            (Default value = False)

        print_level: 0 - None, 1 - just results, 2 - current round and hypothesis size, 3 - educational/debug
            (Default value = 2)

    Returns:

        automaton of type automaton_type (dict containing all information about learning if 'return_data' is True)

    """

    if cache_and_non_det_check or samples is not None:
        # Wrap the sul in the CacheSUL, so that all steps/queries are cached
        if not isinstance(sul, DfaSUL):
            sul = CacheSUL(sul)

        eq_oracle.sul = sul

        if samples:
            for input_seq, output_seq in samples:
                sul.cache.add_to_cache(input_seq, output_seq)

    ob_tree = ObservationTreeSquare(alphabet, sul, automaton_type)
    start_time = time.time()

    eq_query_time = 0
    learning_rounds = 0
    validity_queries = 0
    hypothesis = None

    while True:
        learning_rounds += 1
        if max_learning_rounds and learning_rounds == max_learning_rounds:
            break

        # Building the hypothesis
        hypothesis = ob_tree.build_hypothesis()

        if print_level > 1:
            print(f'Hypothesis {learning_rounds}: {hypothesis.size} states.')
        if print_level == 3:
            print(hypothesis)

        # Pose Equivalence Query
        eq_query_start = time.time()
        cex = eq_oracle.find_cex(hypothesis)
        eq_query_time += time.time() - eq_query_start
        validity_queries += 1

        if print_level > 2:
            print(f'Counterexample: {cex}')

        if cex is None:
            break

        # Process the counterexample and start a new learning round
        cex_output = sul.query(cex)
        ob_tree.process_counter_example(hypothesis, cex, cex_output)

    total_time = time.time() - start_time
    eq_query_time = eq_query_time
    smt_time = ob_tree.smt_time
    learning_time = total_time - eq_query_time - smt_time

    info = {
        'learning_rounds': learning_rounds,
        'automaton_size': hypothesis.size,
        #time
        'learning_time': learning_time,
        'smt_time': smt_time,
        'eq_oracle_time': eq_query_time,
        'total_time': total_time,
        #learning algorithm
        'queries_learning': sul.num_queries,
        'validity_query': validity_queries,
        'rule1': ob_tree.rule1_applications,
        'rule2': ob_tree.rule2_applications,
        'rule3': ob_tree.rule3_applications,
        'rule4': ob_tree.rule4_applications,
        #tree
        'nodes':ob_tree.get_size(),
        'informative_nodes':ob_tree.count_informative_nodes(),
        'analyzed_bases':ob_tree.bases_analyzed,
        # system under learning
        'sul_steps': sul.num_steps,
        'cache_saved': sul.num_cached_queries,
        #eq_oracle
        'queries_eq_oracle': eq_oracle.num_queries,
        'steps_eq_oracle': eq_oracle.num_steps,
    }

    if print_level > 0:
        pretty_print_info(info)

    if return_data:
        return hypothesis, info

    return hypothesis

def pretty_print_info(info: dict):
    """
    Print learning statistics.
    """
    print('-----------------------------------')
    #general
    print('Learning Finished.')
    print('Learning Rounds:  {}'.format(info['learning_rounds']))
    print('Number of states: {}'.format(info['automaton_size']))
    #time
    print('Time (in seconds)')
    print('  Total                : {}'.format(round(info['total_time'], 2)))
    print('  Learning algorithm   : {}'.format(round(info['learning_time'], 2)))
    print('  Smt solver           : {}'.format(round(info['smt_time'], 2)))
    print('  Validity checking    : {}'.format(round(info['eq_oracle_time'], 2)))
    # learning algorithm stats
    print()
    print('Learning Algorithm         ')
    print(' # Membership Queries  : {}'.format(info['queries_learning']))
    print(' # Validity Queries    : {}'.format(info['validity_query']))
    print(' Rule applications         ')
    print('   - Rule 1 applied      : {}'.format(info['rule1']))
    print('   - Rule 2 applied      : {}'.format(info['rule2']))
    print('   - Rule 3 applied      : {}'.format(info['rule3']))
    print('   - Rule 4 applied      : {}'.format(info['rule4']))
    #tree stats
    print()
    print('Tree')
    print(' # Amount of Nodes     : {}'.format(info['nodes']))
    print(' # Informative Nodes   : {}'.format(info['informative_nodes']))
    print(' # Bases Analysed      : {}'.format(info['analyzed_bases']))
    #system under learning
    print()
    print('System under learning      ')
    print(' # MQ Saved by Caching : {}'.format(info['cache_saved']))
    print(' # Steps in automaton  : {}'.format(info['sul_steps']))
    #validity oracle
    print()
    print('Validity Oracle')
    print(' # Membership Queries  : {}'.format(info['queries_eq_oracle']))
    print(' # Steps in automaton  : {}'.format(info['steps_eq_oracle']))
    print('-----------------------------------')