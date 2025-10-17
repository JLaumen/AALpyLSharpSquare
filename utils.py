from aalpy.learning_algs.deterministic.ObservationTable import ObservationTable
from collections import defaultdict
from itertools import combinations
from aalpy.automata import DfaState, Dfa
import numpy as np
from automata.fa.dfa import DFA
from aalpy.utils import make_input_complete, load_automaton_from_file, save_automaton_to_file
from pydot import graph_from_dot_file, Node, Edge
from itertools import product


def get_product_dfa(dfa1, dfa2):
    dfa1 = aalpy_to_automata_lib_format(dfa1)
    dfa2 = aalpy_to_automata_lib_format(dfa2)
    dfa_new_states = set(["-".join([str(i), str(j)]) for i, j in product(dfa1.states, dfa2.states)])
    dfa_new_alphabet = dfa1.input_symbols
    dfa_new_transitions = {}
    for s in dfa_new_states:
        dfa_new_transitions[s] = {}
        for a in dfa_new_alphabet:
            s1, s2 = s.split("-")
            s1_new = dfa1.transitions[int(s1)][a]
            s2_new = dfa2.transitions[int(s2)][a]
            dfa_new_transitions[s][a] = "-".join([str(s1_new), str(s2_new)])
    dfa_new_initial_state = "-".join([str(dfa1.initial_state), str(dfa2.initial_state)])
    dfa_new_final_states = set(["-".join([str(i), str(j)]) for i, j in product(dfa1.final_states, dfa2.final_states) if
                                i in dfa1.final_states and j in dfa2.final_states])
    dfa_new = DFA(states=dfa_new_states,
                  input_symbols=dfa_new_alphabet,
                  transitions=dfa_new_transitions,
                  initial_state=dfa_new_initial_state,
                  final_states=dfa_new_final_states)
    # dfa_new = dfa_new.minify()
    return automata_lib_to_aalpy_format(dfa_new)


def dfa_to_transtion_matrix(dfa):
    l = dfa.states
    S = np.zeros((1, len(l)))
    A = np.zeros((len(l), len(l)))
    F = np.zeros((len(l), 1))
    S[0, dfa.initial_state] = 1
    for i in l:
        if i in dfa.final_states:
            F[i] = 1
        for _, j in dfa.transitions[i].items():
            A[i, j] = 1
    return S, A, F


def aalpy_to_automata_lib_format(dfa):
    d = dict([(v, k) for k, v in enumerate(dfa.states)])
    states = set(d.values())
    input_symbols = set(dfa.get_input_alphabet())
    transitions = {}
    for s, i in d.items():
        transitions[i] = {}
        for a, s2 in s.transitions.items():
            transitions[i][a] = d[s2]
    initial_state = d[dfa.initial_state]
    final_states = set([i for s, i in d.items() if s.is_accepting])
    return DFA(states=states,
               input_symbols=input_symbols,
               transitions=transitions,
               initial_state=initial_state,
               final_states=final_states
               )


def automata_lib_to_aalpy_format(dfa):
    l = {}
    init_index = dfa.initial_state
    for i in dfa.states:
        s = DfaState(str(i))
        s.is_accepting = i in dfa.final_states
        l[str(i)] = s
    for i in dfa.states:
        for a, j in dfa.transitions[i].items():
            l[str(i)].transitions[a] = l[str(j)]
    return Dfa(l[str(init_index)], list(l.values()))


def are_dfa_equivalent(dfa1, dfa2):
    make_input_complete(dfa1, "sink_state")
    make_input_complete(dfa2, "sink_state")
    A = aalpy_to_automata_lib_format(dfa1)
    B = aalpy_to_automata_lib_format(dfa2)
    return A == B


def get_sim_diff_dfa(dfa1, dfa2):
    A = aalpy_to_automata_lib_format(dfa1)
    B = aalpy_to_automata_lib_format(dfa2)
    return A ^ B


def get_diff_dfa(dfa1, dfa2):
    A = aalpy_to_automata_lib_format(dfa1)
    B = aalpy_to_automata_lib_format(dfa2)
    return automata_lib_to_aalpy_format(A - B)


def get_intersection_dfa(dfa1, dfa2):
    A = aalpy_to_automata_lib_format(dfa1)
    B = aalpy_to_automata_lib_format(dfa2)
    C = A & B
    D = automata_lib_to_aalpy_format(C)
    return D


def is_subset(dfa1, dfa2):
    A = aalpy_to_automata_lib_format(dfa1)
    B = aalpy_to_automata_lib_format(dfa2)
    C = A & B
    return C == B


def are_disjoint(dfa1, dfa2):
    A = aalpy_to_automata_lib_format(dfa1)
    B = aalpy_to_automata_lib_format(dfa2)
    C = A & B
    return C.isempty()


def get_union_dfa(dfa1, dfa2):
    A = aalpy_to_automata_lib_format(dfa1)
    B = aalpy_to_automata_lib_format(dfa2)
    C = A | B
    D = automata_lib_to_aalpy_format(C)
    return D


def get_all_groupings(S):
    all_groupings = []
    for i in range(1, len(S) + 1):
        all_groupings.extend(list(combinations(S, i)))
    return all_groupings


def is_group_covering(group, S):
    final = tuple()
    for member in group:
        final += member
    final = set(final)
    return len(final) == len(S)


def rows_closed(row1, row2):
    for i in range(len(row1)):
        if row1[i] in [0, 1] and row2[i] in [0, 1]:
            if row1[i] != row2[i]:
                return False
    return True


def is_group_closed(group, Q):
    for g in group:
        for s1, s2 in combinations(g, 2):
            if not rows_closed(Q[s1], Q[s2]):
                return False
    return True


def build_table(group, Q):
    final_table = defaultdict(tuple)
    for g in group:
        row = tuple()
        for i in range(len(Q[g[0]])):
            found = False
            for s in g:
                if Q[s][i] is not None:
                    row += (bool(Q[s][i]),)
                    found = True
                    break
            if not found:
                row += (True,)  # TODO: marking all unspecified as True
        for s in g:
            final_table[s] = row
    return final_table


def find_minimal_consistent_dfa(observation_table):
    Q = defaultdict(tuple)
    extended_S = list(observation_table.T.keys())

    for s in extended_S:
        for i in range(len(observation_table.E)):
            if observation_table.T[s][i] == "+":
                Q[s] += (1,)
            elif observation_table.T[s][i] == "-":
                Q[s] += (0,)
            else:
                Q[s] += (None,)
    all_groupings = get_all_groupings(extended_S)
    num_of_groups = 1
    while True:
        for group in combinations(all_groupings, num_of_groups):
            if is_group_covering(group, extended_S):
                if is_group_closed(group, Q):
                    final_dfa = ObservationTable(observation_table.alphabet, observation_table.sul, "dfa")
                    final_dfa.S = observation_table.S  # TODO: consider removing duplicate rows
                    final_dfa.E = observation_table.E
                    final_dfa.T = build_table(group, Q)
                    return final_dfa.gen_hypothesis(check_for_duplicate_rows=False)  # TODO: maybe change to True
        num_of_groups += 1


def load_automaton(path, automaton_type, compute_prefixes=False):
    graph = graph_from_dot_file(path)[0]
    graph.add_node(Node('__start0', label="", shape='none'))
    graph.add_edge(Edge('__start0', "0", label=""))
    graph.write_raw(path)
    A = load_automaton_from_file(path, automaton_type, compute_prefixes=compute_prefixes)
    save_automaton_to_file(A, path.replace('.dot', ''))
    return load_automaton_from_file(path, automaton_type, compute_prefixes=compute_prefixes)


def minimize_dfa(dfa):
    A = aalpy_to_automata_lib_format(dfa)
    B = A.minify()
    return automata_lib_to_aalpy_format(B)


def moore_to_dfa(machine, accepting_output):
    d = {}
    for s in machine.states:
        d[s.state_id] = DfaState(s.state_id, is_accepting=s.output==accepting_output)
    for s in machine.states:
        for a, s2 in s.transitions.items():
            d[s.state_id].transitions[a] = d[s2.state_id]
    initial_state = d[machine.initial_state.state_id]
    return Dfa(initial_state, list(d.values()))
