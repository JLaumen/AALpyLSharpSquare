from aalpy.base import SUL
from aalpy.base.Oracle import Oracle
from aalpy.oracles import RandomWMethodEqOracle

from utils import get_intersection_dfa, get_diff_dfa, are_dfa_equivalent, aalpy_to_automata_lib_format, is_subset
from aalpy.automata import Dfa, DfaState
from automata.base.exceptions import EmptyLanguageException

class SULOracleWrapper(SUL):
    def __init__(self, sul, target):
        super().__init__()
        self.sul = sul
        self.target = target

    def pre(self):
        self.sul.pre()

    def post(self):
        self.sul.post()

    def step(self, letter):
        l = self.sul.step(letter)
        return l == self.target

    def query(self, word: tuple) -> list:
        self.pre()
        if len(word) == 0:
            out = [(self.target == False) or (self.target is None)]
        else:
            out = [self.step(letter) for letter in word]
        self.post()
        return out


import sys
class SystemDCOracleST(Oracle):
    def __init__(self, alphabet: list, sul: SUL, T, traces, walks_per_state=200, walk_len=30, example=None, t_type=None):
        super().__init__(alphabet, sul)
        self.T = T
        self.traces = traces
        self.dc1_oracle = RandomWMethodEqOracle(alphabet, SULOracleWrapper(sul, "?"), walks_per_state=walks_per_state, walk_len=walk_len)
        self.b_oracle = RandomWMethodEqOracle(alphabet, SULOracleWrapper(sul, "+"), walks_per_state=walks_per_state, walk_len=walk_len)
        self.t_diff_b_oracle = RandomWMethodEqOracle(alphabet, SULOracleWrapper(sul, "-"), walks_per_state=walks_per_state, walk_len=walk_len)
        self.dc_oracle = RandomWMethodEqOracle(alphabet, SULOracleWrapper(sul, "?"), walks_per_state=walks_per_state, walk_len=walk_len)
        self.equivalence_queries = 0
        self.example = example
        self.t_type = t_type

    def find_cex(self, hypothesis):
        self.equivalence_queries += 1
        for label, trace in self.traces:
            if hypothesis.execute_sequence(hypothesis.initial_state, trace)[-1] != label:
                return trace

        if self.t_type != "2" or self.example not in ["m55", "m135", "m185", "m22", "m199", "m76"]:
            HT = self.moore_to_dfa(hypothesis, "+-")
            if not is_subset(self.T, HT):
                A = aalpy_to_automata_lib_format(HT)
                B = aalpy_to_automata_lib_format(self.T)
                D = A - B
                try:
                    D_k = D.minimum_word_length()
                except EmptyLanguageException:
                    raise Exception("not subset bu cannot find word in diff!")
                for word in D.words_of_length(D_k):
                    return self.str_to_word(word)
        else:
            HT = self.moore_to_dfa(hypothesis, "?")
            cex = self.dc1_oracle.find_cex(HT)
            if cex is not None:
                return cex

        B = self.moore_to_dfa(hypothesis, "+")
        cex = self.b_oracle.find_cex(B)
        if cex is not None:
            return cex
        T_diff_B = self.moore_to_dfa(hypothesis, "-")
        cex = self.t_diff_b_oracle.find_cex(T_diff_B)
        if cex is not None:
            return cex
        DC = self.moore_to_dfa(hypothesis, "?")
        cex = self.dc_oracle.find_cex(DC)
        if cex is not None:
            return cex
        return None

    def reset_hyp_and_sul(self, hypothesis):
        pass

    def moore_to_dfa(self, machine, accepting_output):
        d = {}
        for s in machine.states:
            d[s.state_id] = DfaState(s.state_id, is_accepting=s.output in accepting_output)
        for s in machine.states:
            for a, s2 in s.transitions.items():
                d[s.state_id].transitions[a] = d[s2.state_id]
        initial_state = d[machine.initial_state.state_id]
        return Dfa(initial_state, list(d.values()))

    def str_to_word(self, s):
        l = []
        while len(s) > 0:
            for a in self.alphabet:
                if s.startswith(a):
                    l.append(a)
                    s = s[len(a):]
        return tuple(l)
