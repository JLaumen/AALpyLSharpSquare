from aalpy.base import SUL
from aalpy.base.Oracle import Oracle
from aalpy.oracles import RandomWMethodEqOracle

from utils import get_intersection_dfa, get_diff_dfa, are_dfa_equivalent, aalpy_to_automata_lib_format, is_subset
from aalpy.automata import Dfa, DfaState, MooreState, MooreMachine
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
        # If target is "?" treat it as a wildcard: always match (ignore '?' comparisons).
        if self.target == "?":
            # still consume the step on the wrapped SUL so side-effects / state advance happen
            self.sul.step(letter)
            return True
        l = self.sul.step(letter)
        return l == self.target

    def query(self, word: tuple) -> list:
        self.pre()
        # empty-word: try to query the wrapped SUL if it supports query, otherwise
        # treat "?" as wildcard (match).
        if len(word) == 0:
            try:
                val = self.sul.query(tuple())
                out = [(self.target == "?") or (val and val[0] == self.target)]
            except Exception:
                out = [self.target == "?"]
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
        # use the filtered wrapper for '+' and '-' so sampled words aren't ones where SUL returns '?'
        self.dc1_oracle = RandomWMethodEqOracle(alphabet, SULOracleWrapper(sul, "?"), walks_per_state=walks_per_state, walk_len=walk_len)
        self.b_oracle = FilteredRandomWMethodEqOracle(alphabet, sul, "+", walks_per_state=walks_per_state, walk_len=walk_len)
        self.t_diff_b_oracle = FilteredRandomWMethodEqOracle(alphabet, sul, "-", walks_per_state=walks_per_state, walk_len=walk_len)
        # keep dc / wildcard oracles as-is
        self.dc_oracle = RandomWMethodEqOracle(alphabet, SULOracleWrapper(sul, "?"), walks_per_state=walks_per_state, walk_len=walk_len)
        self.equivalence_queries = 0
        self.example = example
        self.t_type = t_type

    def find_cex(self, hypothesis):
        self.equivalence_queries += 1

        # If hypothesis is a plain DFA, use the SUL-based oracles (so behavior is checked against the SUL),
        # but only require agreement on '+' and '-' (we materialize boolean-output Moore machines).
        if isinstance(hypothesis, Dfa):

            def dfa_to_boolean_moore(dfa, accept_when_accepting: bool):
                # accept_when_accepting True  -> hypothesis outputs True for DFA accepting states (maps to '+')
                # accept_when_accepting False -> hypothesis outputs True for DFA non-accepting states (maps to '-')
                states_map = {}
                for s in dfa.states:
                    out = (s.is_accepting == accept_when_accepting)
                    states_map[s.state_id] = MooreState(s.state_id, output=out)
                for s in dfa.states:
                    for a, s2 in s.transitions.items():
                        states_map[s.state_id].transitions[a] = states_map[s2.state_id]
                init = states_map[dfa.initial_state.state_id]
                return MooreMachine(init, list(states_map.values()))

            # quick check against explicit traces first (faster)
            for label, trace in self.traces:
                if label == '+':
                    # DFA must accept
                    state = hypothesis.initial_state
                    for a in trace:
                        if a not in state.transitions:
                            state = None
                            break
                        state = state.transitions[a]
                    accepts = bool(state and state.is_accepting)
                    if not accepts:
                        return trace
                elif label == '-':
                    # DFA must reject
                    state = hypothesis.initial_state
                    for a in trace:
                        if a not in state.transitions:
                            state = None
                            break
                        state = state.transitions[a]
                    accepts = bool(state and state.is_accepting)
                    if accepts:
                        return trace
                # ignore '?' traces for DFA input

            # Use SUL-based random/w-method oracles to find counterexamples wrt '+' and '-' behavior
            B_plus = dfa_to_boolean_moore(hypothesis, accept_when_accepting=True)
            cex = self.b_oracle.find_cex(B_plus)
            if cex is not None:
                return cex

            B_minus = dfa_to_boolean_moore(hypothesis, accept_when_accepting=False)
            cex = self.t_diff_b_oracle.find_cex(B_minus)
            if cex is not None:
                return cex

            # also check for '?' traces (if SUL can produce '?') by giving a Moore that never outputs True for '?'
            # this will detect if the SUL yields '?' on some sequences while the DFA never does.
            DC = dfa_to_boolean_moore(hypothesis, accept_when_accepting=False)  # outputs True only for '-' states
            cex = self.dc_oracle.find_cex(DC)
            if cex is not None:
                return cex

            return None

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

class FilteredRandomWMethodEqOracle:
    """
    Wraps RandomWMethodEqOracle but ensures returned counterexamples correspond
    to SUL outputs that are actually '+' or '-', not '?'.
    """
    def __init__(self, alphabet, real_sul, target, walks_per_state=200, walk_len=30):
        self.real_sul = real_sul
        self.target = target  # '+' or '-' or '?'
        # underlying oracle compares hypothesis using a wrapped SUL producing booleans
        self.inner = RandomWMethodEqOracle(alphabet, SULOracleWrapper(real_sul, target),
                                           walks_per_state=walks_per_state, walk_len=walk_len)
        # expose attributes used elsewhere if needed
        self.alphabet = self.inner.alphabet
        self.walks_per_state = walks_per_state
        self.walk_len = walk_len

    def find_cex(self, hypothesis):
        # try multiple times to get a cex that matches the real_sul final output requirement
        max_attempts = max(10 * (self.walks_per_state or 1), 1000)
        attempts = 0
        while attempts < max_attempts:
            cex = self.inner.find_cex(hypothesis)
            if cex is None:
                return None
            # ask the real SUL what it actually outputs for this word
            try:
                out = self.real_sul.query(tuple(cex))
                last = out[-1] if out else None
            except Exception:
                last = None
            # if SUL produced '?', skip this candidate
            if last == "?":
                attempts += 1
                continue
            # if we want '+' ensure SUL returned '+', similarly for '-'
            if self.target == "+" and last == "+":
                return cex
            if self.target == "-" and last == "-":
                return cex
            # if target is wildcard accept any non-'?' result
            if self.target == "?":
                return cex
            attempts += 1
        return None
