from aalpy.base import SUL
from aalpy.automata.Dfa import Dfa
from aalpy.base.CacheTree import CacheTree, CacheDict


class RCSUL(SUL):

    def __init__(self, spec_dfa: Dfa, system_dfa: Dfa, failed_tests, passed_tests):
        super().__init__()
        self.spec_dfa = spec_dfa
        self.system_dfa = system_dfa
        self.failed_tests = failed_tests
        # prefix closure
        # self.passed_tests = {tuple()}
        # for p in passed_tests:
        #     for i in range(len(p)):
        #         self.passed_tests.add(p[:i + 1])
        self.passed_tests = passed_tests
        self.num_queries = 0
        self.membership_queries = 0
        self.num_steps = 0
        self.system_queries = 0
        self.already_not_in_system = False
        self.already_failed_in_system = False
        self.prefix = []
        self.cache = CacheTree()

    def query(self, word: tuple) -> list:
        if type(word) == list:
            word = tuple(word)
        self.num_queries += 1
        self.membership_queries += 1
        self.num_steps += len(word)
        final_result = None
        if len(word) == 0:
            return ["-"]
        else:
            in_system = self.spec_dfa.execute_sequence(self.spec_dfa.initial_state, word)
        # if isinstance(in_system, list) and not in_system[-1]:
        #     for i in range(len(word)):
        #         if not in_system[i]:
        #             p = []
        #             if i > 0:
        #                 p = self.system_dfa.execute_sequence(self.system_dfa.initial_state, word[:i])
        #             q = ["?"] * len(word[i:])
        #             final_result = ["+" if x else "-" for x in p] + q
        #             break
        if word in self.failed_tests:
            failed_in_system = self.system_dfa.execute_sequence(self.system_dfa.initial_state, word)
            final_result = ["+" if x else "-" for x in failed_in_system]
            final_result = [x if y else "?" for x, y in zip(final_result, in_system)]
        else:
            self.system_queries += 1
            if len(word) == 0:
                failed_in_system = self.system_dfa.initial_state.is_accepting
                final_result = ["+" if x else "-" for x in [failed_in_system]]
            else:
                failed_in_system = self.system_dfa.execute_sequence(self.system_dfa.initial_state, word)
                final_result = ["+" if x else "-" for x in failed_in_system]
                final_result = [x if y else "?" for x, y in zip(final_result, in_system)]

        cached_query = self.cache.in_cache(word)
        if cached_query:
            if cached_query != tuple(final_result):
                raise Exception("Cached query is not the same as the result of the query on word", word, cached_query, final_result)
        self.cache.reset()
        for i, o in zip(word, final_result):
            self.cache.step_in_cache(i, o)

        return final_result




    def pre(self):
        self.spec_dfa.reset_to_initial()
        self.system_dfa.reset_to_initial()
        self.already_not_in_system = False
        self.already_failed_in_system = False
        self.prefix = []

    def post(self):
        pass

    def step(self, letter):
        self.num_steps += 1
        self.prefix.append(letter)
        in_system = self.spec_dfa.step(letter)
        # change if you want to use prefix closure
        if not in_system:
            return "?"
        self.system_queries += 1
        failed_in_system = self.system_dfa.step(letter)
        if failed_in_system or self.already_failed_in_system:
            self.already_failed_in_system = True
            return "+"
        else:
            return "-"