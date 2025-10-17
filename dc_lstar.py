import time

from aalpy.base import Oracle, SUL
from aalpy.utils.HelperFunctions import extend_set, print_learning_info, print_observation_table, all_prefixes
from aalpy.learning_algs.deterministic.CounterExampleProcessing import longest_prefix_cex_processing, rs_cex_processing
from aalpy.learning_algs.deterministic.ObservationTable import ObservationTable
from aalpy.base.SUL import CacheSUL

counterexample_processing_strategy = [None, 'rs', 'longest_prefix']
closedness_options = ['prefix', 'suffix']
print_options = [0, 1, 2, 3]


def run_Lstar(alphabet: list, sul: SUL, eq_oracle: Oracle, automaton_type,
              closing_strategy='longest_first', cex_processing='rs', suffix_closedness=True, closedness_type='suffix',
              max_learning_rounds=None, cache_and_non_det_check=True, return_data=False, print_level=2):

    assert cex_processing in counterexample_processing_strategy
    assert closedness_type in closedness_options
    assert print_level in print_options
    cex = None

    if cache_and_non_det_check:
        # Wrap the sul in the CacheSUL, so that all steps/queries are cached
        sul = CacheSUL(sul)
        eq_oracle.sul = sul

    start_time = time.time()
    eq_query_time = 0
    learning_rounds = 0
    hypothesis = None

    observation_table = ObservationTable(alphabet, sul, automaton_type)

    # Initial update of observation table, for empty row
    observation_table.update_obs_table()
    while True:
        learning_rounds += 1
        if max_learning_rounds and learning_rounds - 1 == max_learning_rounds:
            break

        # Make observation table consistent (iff there is no counterexample processing)
        if not cex_processing:
            inconsistent_rows = observation_table.get_causes_of_inconsistency()

            while inconsistent_rows is not None:
                extend_set(observation_table.E, inconsistent_rows)
                observation_table.update_obs_table(e_set=inconsistent_rows)
                new_inconsistent_rows = observation_table.get_causes_of_inconsistency()
                inconsistent_rows = new_inconsistent_rows

        # Close observation table
        rows_to_close = observation_table.get_rows_to_close(closing_strategy)
        while rows_to_close is not None:
            rows_to_query = []
            for row in rows_to_close:
                observation_table.S.append(row)
                rows_to_query.extend([row + (a,) for a in alphabet])
            observation_table.update_obs_table(s_set=rows_to_query)
            rows_to_close = observation_table.get_rows_to_close(closing_strategy)

        # Generate hypothesis
        hypothesis = observation_table.gen_hypothesis(no_cex_processing_used=cex_processing is None)

        if print_level > 1:
            print(f'Hypothesis {learning_rounds}: {len(hypothesis.states)} states.')

        if print_level == 3:
            print(hypothesis)
            # print_observation_table(observation_table, 'det')

        # Find counterexample
        eq_query_start = time.time()
        cex = eq_oracle.find_cex(hypothesis)
        # print(cex)
        eq_query_time += time.time() - eq_query_start

        # If no counterexample is found, return the hypothesis
        if cex is None:
            break

        if print_level == 1:
            print('Counterexample', cex)
            print(hypothesis.states.__len__())

        # Process counterexample and ask membership queries
        if not cex_processing:
            s_to_update = []
            added_rows = extend_set(observation_table.S, all_prefixes(cex))
            s_to_update.extend(added_rows)
            for p in added_rows:
                s_to_update.extend([p + (a,) for a in alphabet])

            observation_table.update_obs_table(s_set=s_to_update)
            continue
        elif cex_processing == 'longest_prefix':
            cex_suffixes = longest_prefix_cex_processing(observation_table.S + list(observation_table.s_dot_a()),
                                                         cex, closedness_type)
        else:
            cex_suffixes = rs_cex_processing(sul, cex, hypothesis, suffix_closedness, closedness_type)

        added_suffixes = extend_set(observation_table.E, cex_suffixes)
        observation_table.update_obs_table(e_set=added_suffixes)

    total_time = round(time.time() - start_time, 5)
    eq_query_time = round(eq_query_time, 5)
    learning_time = round(total_time - eq_query_time, 5)

    info = {
        'learning_rounds': learning_rounds,
        'automaton_size': len(hypothesis.states),
        'queries_learning': sul.num_queries,
        'steps_learning': sul.num_steps,
        'queries_eq_oracle': eq_oracle.num_queries,
        'steps_eq_oracle': eq_oracle.num_steps,
        'learning_time': learning_time,
        'eq_oracle_time': eq_query_time,
        'total_time': total_time,
        'characterization set': observation_table.E,
        'observation_table': observation_table,
        'membership_queries': sul.membership_queries,
        'equivalence_queries': eq_oracle.equivalence_queries,
        'system_queries': sul.system_queries
    }
    if cache_and_non_det_check:
        info['cache_saved'] = sul.num_cached_queries

    if print_level > 0:
        print_learning_info(info)

    if return_data:
        return hypothesis, info

    return hypothesis
