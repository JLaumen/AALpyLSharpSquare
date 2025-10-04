import time

from aalpy.base import Oracle, SUL
from .ObservationTreeSquare import ObservationTreeSquare
from ...base.SUL import CacheSUL


def run_lsharp_square(alphabet: list,
                      sul: SUL,
                      eq_oracle: Oracle,
                      cache_and_non_det_check: bool = True,
                      return_data: bool = False):
    if cache_and_non_det_check:
        # Wrap the sul in the CacheSUL, so that all steps/queries are cached
        sul = CacheSUL(sul)

        eq_oracle.sul = sul

    ob_tree = ObservationTreeSquare(alphabet, sul)
    start_time = time.time()

    eq_query_time = 0
    learning_rounds = 0
    validity_queries = 0
    hypothesis = None

    while True:
        learning_rounds += 1

        # Limit to one hour
        if time.time() - start_time > 3600:
            break

        # Building the hypothesis
        hypothesis = ob_tree.build_hypothesis()

        if hypothesis is None:
            continue

        # Pose Equivalence Query
        eq_query_start = time.time()
        cex = eq_oracle.find_cex(hypothesis)
        eq_query_time += time.time() - eq_query_start
        validity_queries += 1

        if cex is None:
            break

        # Process the counterexample and start a new learning round
        cex_output = sul.query(cex)
        ob_tree.process_counter_example(cex, cex_output)

    total_time = time.time() - start_time
    smt_time = ob_tree.smt_time
    learning_time = total_time - eq_query_time - smt_time

    info = {
        'learning_rounds': learning_rounds,
        'automaton_size': hypothesis.size,
        # time
        'learning_time': learning_time,
        'smt_time': smt_time,
        'eq_oracle_time': eq_query_time,
        'total_time': total_time,
        # learning algorithm
        'queries_learning': sul.num_queries,
        'validity_query': validity_queries,
        # tree
        'nodes': ob_tree.get_size(),
        'informative_nodes': ob_tree.count_informative_nodes(),
        # system under learning
        'sul_steps': sul.num_steps,
        'cache_saved': sul.num_cached_queries,
        # eq_oracle
        'queries_eq_oracle': eq_oracle.num_queries,
        'steps_eq_oracle': eq_oracle.num_steps,
    }

    if return_data:
        return hypothesis, info

    return hypothesis
