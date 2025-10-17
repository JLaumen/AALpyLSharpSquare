import concurrent.futures
import datetime
import logging
import os
from typing import Any

from aalpy.SULs import IncompleteDfaSUL
from aalpy.learning_algs import run_lsharp_square
from aalpy.oracles import ValidityDataOracle
from aalpy.utils import generate_random_dfa

import random

class DFA:
    def __init__(self, num_states, alphabet):
        self.num_states = num_states
        self.alphabet = alphabet
        self.transitions = [{a: random.randint(0, num_states - 1) for a in alphabet} for _ in range(num_states)]
        self.accepting = set(random.sample(range(num_states), random.randint(1, num_states)))
        self.initial_state = 0

    def accepts(self, word):
        state = self.initial_state
        for symbol in word:
            state = self.transitions[state][symbol]
        return state in self.accepting

def generate_random_dfa_test_file(n, filename):
    dfa = DFA(n, ['0', '1'])
    seen = set()
    with open(filename, 'w') as f:
        for _ in range(100):
            word = ''.join(random.choice(['0', '1']) for _ in range(20))
            for i in range(0, len(word) + 1):
                prefix = word[:i]
                if prefix in seen:
                    continue
                seen.add(prefix)
                accepted = dfa.accepts(prefix)
                f.write(f"{prefix},{'+' if accepted else '-'}\n")

# From the Aalpy folder, run using:
# PYTHONPATH=. python3 Benchmarking/incomplete_dfa_benchmark/benchmark_incomplete_dfa.py

test_cases_path = "Benchmarking/incomplete_dfa_benchmark/test_cases/"
logging.basicConfig(level=logging.INFO, format=f"%(asctime)s %(levelname)s: %(message)s", datefmt="%H:%M:%S")


def is_simple_input(inp: str) -> bool:
    return all(c in ["0", "1", "X"] for c in inp)


def get_possible_words(prefix: str, suffix: str, alphabet: list) -> list:
    words = []
    if suffix:
        if suffix[0] == "X":
            for letter in alphabet:
                words.extend(get_possible_words(prefix + letter, suffix[1:], alphabet))
        else:
            letter = suffix[0]
            words.extend(get_possible_words(prefix + letter, suffix[1:], alphabet))
        return words
    else:
        return [prefix]


def parse_file(filename: str, alphabet: list, horizon: int | None = None) -> tuple[list, list]:
    with open(test_cases_path + filename, 'r') as f:
        known_words = []
        observed_alphabet = []
        for l in f:
            split_index = l.strip().rfind(',')
            inp = l.strip()[:split_index]
            out = l.strip()[split_index + 1:]
            out = out.strip() == "+"
            if is_simple_input(inp):
                inputs = get_possible_words("", inp, alphabet)
                for word in inputs:
                    for letter in word:
                        if not letter in observed_alphabet:
                            observed_alphabet.append(letter)
                    known_words.append((word, out))
            else:
                word = inp.split(";")
                for letter in word:
                    if not letter in observed_alphabet:
                        observed_alphabet.append(letter)
                if horizon is None or len(word) <= horizon:
                    known_words.append((word, out))

        return known_words, observed_alphabet


def run_test_case(filename: str, horizon: int | None = None) -> dict[str, Any]:
    alphabet = [True, False]
    data, alphabet = parse_file(filename, alphabet, horizon)
    sul = IncompleteDfaSUL(data.copy())
    eq_oracle = ValidityDataOracle(data.copy())

    learned_dfa, info = run_lsharp_square(alphabet, sul, eq_oracle, return_data=True)

    successful = eq_oracle.find_cex(learned_dfa) is None
    info["successful"] = successful
    return info


def run_test_case_horizon_increase(file_name: str, max_horizon: int | None = None) -> None:
    with open(f"Benchmarking/incomplete_dfa_benchmark/benchmark3_{file_name.replace('/', '_')}.csv", "w") as f:
        f.write("horizon,file_name,succeeded,learning_rounds,automaton_size,learning_time,"
                "smt_time,eq_oracle_time,total_time,queries_learning,validity_query,nodes,"
                "informative_nodes,sul_steps,queries_eq_oracle,steps_eq_oracle\n")

        for horizon in range(1, max_horizon + 1):
            logging.info(f"Testing {file_name} with horizon={horizon}")
            info = run_test_case(f"AAL-benchmarks/{file_name}", horizon=horizon)
            f.write(','.join([str(horizon),
                              file_name,
                              str(info['successful']),
                              str(info['learning_rounds']),
                              str(info['automaton_size']),
                              str(info['learning_time']),
                              str(info['smt_time']),
                              str(info['eq_oracle_time']),
                              str(info['total_time']),
                              str(info['queries_learning']),
                              str(info['validity_query']),
                              str(info['nodes']),
                              str(info['informative_nodes']),
                              str(info['sul_steps']),
                              str(info['queries_eq_oracle']),
                              str(info['steps_eq_oracle'])]) + "\n")
            logging.info(f"Finished testing {file_name}")
            logging.info(f"Time: {info['total_time']}")
            logging.info(f"Queries: {info['queries_learning']}")
            logging.info(f"Validity: {info['validity_query']}")
            logging.info(f"Size: {info['automaton_size']}")
            if not info['successful']:
                break


def process_file(file_name: str, target_folder: str) -> str:
    logging.info(f"Testing {file_name}")
    info = run_test_case(f"oliveira/{target_folder}/{file_name}")
    row = ','.join([f"oliveira/{target_folder}/{file_name}",
                    str(info['successful']),
                    str(info['learning_rounds']),
                    str(info['automaton_size']),
                    str(info['learning_time']),
                    str(info['smt_time']),
                    str(info['eq_oracle_time']),
                    str(info['total_time']),
                    str(info['queries_learning']),
                    str(info['validity_query']),
                    str(info['nodes']),
                    str(info['informative_nodes']),
                    str(info['sul_steps']),
                    str(info['queries_eq_oracle']),
                    str(info['steps_eq_oracle'])]) + "\n"
    logging.info(f"Finished testing {file_name}")
    logging.info(f"Time: {info['total_time']}")
    logging.info(f"Queries: {info['queries_learning']}")
    logging.info(f"Validity: {info['validity_query']}")
    logging.info(f"Size: {info['automaton_size']}")
    return row


def run_test_cases_pool(file: str) -> None:
    with open(f"Benchmarking/incomplete_dfa_benchmark/benchmark_{file}.csv", "w") as f:
        f.write("file name,succeeded,learning_rounds,automaton_size,learning_time,"
                "smt_time,eq_oracle_time,total_time,queries_learning,validity_query,nodes,"
                "informative_nodes,sul_steps,queries_eq_oracle,steps_eq_oracle\n")
        oliveira = test_cases_path + "oliveira/"
        target_folder = file
        folder_path = os.path.join(oliveira, target_folder)
        file_names = sorted(os.listdir(folder_path))

        with concurrent.futures.ProcessPoolExecutor() as executor:
            results = list(executor.map(process_file, file_names, [target_folder] * len(file_names)))
            for row in results:
                f.write(row)


def main() -> None:
    # for i in range(1, 12):
    #     for j in range(1, 101):
    #         generate_random_dfa_test_file(i,
    #                                       f"Benchmarking/incomplete_dfa_benchmark/test_cases/oliveira/random/{i}_{j}.txt")
    run_test_cases_pool("04_11")
    # run_test_case_horizon_increase("SnL-milton-16.txt", max_horizon=11)
    # run_test_case_horizon_increase("airportA3-3-3-15.txt", max_horizon=16)
    return

if __name__ == "__main__":
    main()
