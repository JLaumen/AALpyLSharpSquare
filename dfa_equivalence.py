from aalpy.utils import load_automaton_from_file, save_automaton_to_file, make_input_complete
import numpy as np
from random import choice, random

from utils import get_sim_diff_dfa, dfa_to_transtion_matrix


def get_dfas_distance(dfa1, dfa2):
    sim_dif = get_sim_diff_dfa(dfa1, dfa2)
    S, A, F = dfa_to_transtion_matrix(sim_dif)
    B = (1/(2*len(dfa1.get_input_alphabet())))*A
    C = np.linalg.inv(np.eye(A.shape[0]) - B)
    return np.matmul(np.matmul(S, C), F)[0][0]


def sample_based_dfa_equivalence(M, dfa1, dfa2, n=1000, stop_prob=0.2):
    equivalent = 0
    for i in range(n):
        w = []
        M.reset_to_initial()
        while True:
            w.append(choice(M.current_state.get_diff_state_transitions() + M.current_state.get_same_state_transitions()))
            if random() <= stop_prob:
                break
        if dfa1.execute_sequence(dfa1.initial_state, w)[-1] == dfa2.execute_sequence(dfa2.initial_state, w)[-1]:
            equivalent += 1
    return equivalent/n

if __name__ == '__main__':
    B1 = load_automaton_from_file("output/a.dot", automaton_type='dfa')
    B2 = load_automaton_from_file("output/b.dot", automaton_type='dfa')
    make_input_complete(B1, 'sink_state')
    make_input_complete(B2, 'sink_state')
    print(get_dfas_distance(B1, B2))
    print(sample_based_dfa_equivalence(B1, B2))


