from utils import get_intersection_dfa, get_diff_dfa, aalpy_to_automata_lib_format, is_subset, are_disjoint
from aalpy.automata import Dfa, DfaState

class CompleteDFAOracle:
    def __init__(self, alphabet, dfa3):
        # self.M = M
        self.alphabet = alphabet
        self.M_intersect_B = self.moore_to_dfa(dfa3, "+")
        self.M_diff_B = self.moore_to_dfa(dfa3, "-")
        self.equivalence_queries = 0

    def find_cex(self, hypothesis):
        if set(hypothesis.get_input_alphabet()) != set(self.M_intersect_B.get_input_alphabet()):
            print(set(hypothesis.get_input_alphabet()), set(self.M_intersect_B.get_input_alphabet()))
        self.equivalence_queries += 1
        if not is_subset(hypothesis, self.M_intersect_B):
            A = aalpy_to_automata_lib_format(hypothesis)
            B = aalpy_to_automata_lib_format(self.M_intersect_B)
            D = B - A
            for word in D.words_of_length(D.minimum_word_length()):
                return self.str_to_word(word)
        elif not are_disjoint(hypothesis, self.M_diff_B):
            A = aalpy_to_automata_lib_format(hypothesis)
            B = aalpy_to_automata_lib_format(self.M_diff_B)
            D = B & A
            for word in D.words_of_length(D.minimum_word_length()):
                return self.str_to_word(word)
        else:
            return None

    def str_to_word(self, s):
        l = []
        while len(s) > 0:
            for a in self.alphabet:
                if s.startswith(a):
                    l.append(a)
                    s = s[len(a):]
        return tuple(l)

    def moore_to_dfa(self, machine, accepting_output):
        d = {}
        for s in machine.states:
            d[s.state_id] = DfaState(s.state_id, is_accepting=s.output==accepting_output)
        for s in machine.states:
            for a, s2 in s.transitions.items():
                d[s.state_id].transitions[a] = d[s2.state_id]
        initial_state = d[machine.initial_state.state_id]
        return Dfa(initial_state, list(d.values()))
