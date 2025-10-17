from aalpy.base.Oracle import Oracle
from rc_sul import RCSUL
from aalpy.automata.MooreMachine import MooreMachine
from random import randint, choice

class RCOracle(Oracle):
    def __init__(self, alphabet, sul, oracle):
        self.alphabet = alphabet
        self.sul = sul
        self.num_queries = 0
        self.num_steps = 0
        self.oracle = oracle
        self.equivalence_queries = 0

    def find_cex(self, hypothesis: MooreMachine):
        self.equivalence_queries += 1
        for failed_test in self.sul.failed_tests:
            if len(failed_test) == 0:
                result = hypothesis.initial_state.output
            else:
                result = hypothesis.execute_sequence(hypothesis.initial_state, failed_test)[-1]
            self.num_queries += 1
            self.num_steps += len(failed_test)
            if result != "+":
                return failed_test

        for passed_test in self.sul.passed_tests:
            if len(passed_test) == 0:
                result = hypothesis.initial_state.output
            else:
                result = hypothesis.execute_sequence(hypothesis.initial_state, passed_test)[-1]
            self.num_queries += 1
            self.num_steps += len(passed_test)
            if result != "-":
                return passed_test
        return self.oracle.find_cex(hypothesis)


class SampleBasedRCOracle(Oracle):
    def __init__(self, alphabet, sul: RCSUL, sample_size=50, min_walk_len=5, max_sample_len=20):
        self.alphabet = alphabet
        self.sul = sul
        self.num_queries = 0
        self.num_steps = 0
        self.sample_size = sample_size
        self.min_walk_len = min_walk_len
        self.max_sample_len = max_sample_len

    def find_cex(self, hypothesis: MooreMachine):
        num_samples_done = 0
        sample_lengths = [randint(self.min_walk_len, self.max_sample_len) for _ in range(self.sample_size)]
        while num_samples_done < self.sample_size:
            inputs = []
            hypothesis.reset_to_initial()
            self.sul.spec_dfa.reset_to_initial()
            num_samples_done += 1
            num_steps = sample_lengths.pop(0)
            self.num_queries += 1
            for _ in range(num_steps):
                self.num_steps += 1
                inputs.append(choice(self.sul.spec_dfa.current_state.get_diff_state_transitions() + self.sul.spec_dfa.current_state.get_same_state_transitions()))
                out_spec = self.sul.spec_dfa.step(inputs[-1])
                out_hyp = hypothesis.step(inputs[-1])
                if out_hyp == "+":
                    check = self.sul.query(tuple(inputs))
                    if check[-1] != "+":  # maybe should be less restrictive
                        return inputs

        num_samples_done = 0
        sample_lengths = [randint(self.min_walk_len, self.max_sample_len) for _ in range(self.sample_size)]
        while num_samples_done < self.sample_size:
            inputs = []
            hypothesis.reset_to_initial()
            self.sul.spec_dfa.reset_to_initial()
            num_samples_done += 1
            num_steps = sample_lengths.pop(0)
            self.num_queries += 1
            for _ in range(num_steps):
                self.num_steps += 1
                inputs.append(choice(self.sul.spec_dfa.current_state.get_diff_state_transitions() + self.sul.spec_dfa.current_state.get_same_state_transitions()))
                out_spec = self.sul.spec_dfa.step(inputs[-1])
                out_hyp = hypothesis.step(inputs[-1])
                if out_spec:
                    check = self.sul.query(tuple(inputs))
                    if check[-1] != out_hyp: # maybe should be less restrictive
                        return inputs

