from typing import Tuple
import z3



class FALearner:
    def __init__(self, encoder, oracle, alphabet, max_states, use_all_traces, binary_search, minimize_self_loops, solver=None, verbose=False):
        self.timeout = None
        if not solver:
            solver = z3.Solver()
        self.solver = solver
        self.encoder = encoder
        self.oracle = oracle
        self.verbose = verbose
        self.alphabet = alphabet
        self.max_states = max_states
        self.use_all_traces = use_all_traces
        self.binary_search = binary_search
        self.minimize_self_loops = minimize_self_loops
        self.min_states = 1

    def add(self, trace):
        self.encoder.add(trace)

    def model(self, old_definition=None, ensure_min=False):
        if old_definition is not None:  # TODO: make sure this is correct
            self.min_states = len(old_definition.states)
        (succ, fa, m) = self._learn_model()
        # print(m)
        self.solver.reset()
        if succ:
            return fa.export(m), fa
        else:
            return None

    def _learn_model(self):
        """generates the definition and model for an fa whose traces include the traces added so far
        In case of failure, the second argument of the tuple signals occurrence of a timeout"""
        if self.binary_search:
            low = self.min_states
            high = self.max_states
            optimal_state_num = self.max_states
            while low <= high:
                mid = (low + high) // 2
                fa, constraints = self.encoder.build(mid, mid * len(self.alphabet) + 1, mid * len(self.alphabet) + 1)
                self.solver.reset()
                self.solver.set(":random-seed", 0)
                self.solver.add(constraints)
                if self.timeout is not None:
                    self.solver.set("timeout", self.timeout)
                result = self.solver.check()
                if self.verbose:
                    print("Learning with {0} states. Result: {1}"
                          .format(mid, result))
                if result == z3.sat:
                    optimal_state_num = mid
                    high = mid - 1
                else:
                    low = mid + 1
            low = 1
            high = optimal_state_num * len(self.alphabet) + 1
            optimal_transition_num = optimal_state_num * len(self.alphabet) + 1
            while low <= high:
                mid = (low + high) // 2
                fa, constraints = self.encoder.build(optimal_state_num, mid, optimal_state_num * len(self.alphabet) + 1)
                self.solver.reset()
                self.solver.set(":random-seed", 0)
                self.solver.add(constraints)
                if self.timeout is not None:
                    self.solver.set("timeout", self.timeout)
                result = self.solver.check()
                if self.verbose:
                    print("Learning with {0} transitions. Result: {1}"
                          .format(mid, result))
                if result == z3.sat:
                    optimal_transition_num = mid
                    high = mid - 1
                else:
                    low = mid + 1
            if self.minimize_self_loops:
                low = 1
                high = optimal_state_num * len(self.alphabet) + 1
                optimal_transition_num_second = optimal_state_num * len(self.alphabet) + 1
                while low <= high:
                    mid = (low + high) // 2
                    fa, constraints = self.encoder.build(optimal_state_num, optimal_transition_num, mid)
                    self.solver.reset()
                    self.solver.set(":random-seed", 0)
                    self.solver.add(constraints)
                    if self.timeout is not None:
                        self.solver.set("timeout", self.timeout)
                    result = self.solver.check()
                    if self.verbose:
                        print("Learning with {0} transitions. Result: {1}"
                              .format(mid, result))
                    if result == z3.sat:
                        optimal_transition_num_second = mid
                        high = mid - 1
                    else:
                        low = mid + 1
            else:
                optimal_transition_num_second = optimal_state_num * len(self.alphabet) + 1
            #print(optimal_transition_num)
            fa, constraints = self.encoder.build(optimal_state_num, optimal_transition_num, optimal_transition_num_second)
            self.solver.reset()
            self.solver.set(":random-seed", 0)
            self.solver.add(constraints)
            result = self.solver.check()
            model = self.solver.model()
            dfa = fa
            #print("evaluate",model.evaluate(z3.Sum([z3.If(z3.Or(dfa.transition(state, label) == dfa.states[-1], dfa.transition(state, label) == state), 0, 1) for state in dfa.states for label in dfa.labels.values()])))
            return True, fa, model
        else:
            for num_states in range(self.min_states, self.max_states + 1):
                fa, constraints = self.encoder.build(num_states, num_states * len(self.alphabet) + 1, num_states * len(self.alphabet) + 1)
                self.solver.reset()
                self.solver.set(":random-seed", 0)
                self.solver.add(constraints)
                if self.timeout is not None:
                    self.solver.set("timeout", self.timeout)
                result = self.solver.check()
                if self.verbose:
                    print("Learning with {0} states. Result: {1}"
                          .format(num_states, result))
                if result == z3.sat:
                    for num_transition in range(1, num_states * len(self.alphabet) + 1):
                        fa, constraints = self.encoder.build(num_states, num_transition, num_states * len(self.alphabet) + 1)
                        self.solver.reset()
                        self.solver.set(":random-seed", 0)
                        self.solver.add(constraints)
                        if self.timeout is not None:
                            self.solver.set("timeout", self.timeout)
                        result = self.solver.check()
                        if self.verbose:
                            print("Learning with {0} states. Result: {1}"
                                  .format(num_states, result))
                        if result == z3.sat:
                            if self.minimize_self_loops:
                                for num_transition_second in range(1, num_states * len(self.alphabet) + 1):
                                    fa, constraints = self.encoder.build(num_states, num_transition, num_transition_second)
                                    self.solver.reset()
                                    self.solver.set(":random-seed", 0)
                                    self.solver.add(constraints)
                                    if self.timeout is not None:
                                        self.solver.set("timeout", self.timeout)
                                    result = self.solver.check()
                                    if self.verbose:
                                        print("Learning with {0} states. Result: {1}"
                                              .format(num_states, result))
                                    if result == z3.sat:
                                        model = self.solver.model()
                                        return True, fa, model
                            else:
                                model = self.solver.model()
                                return True, fa, model
            return False, False, None

    def set_timeout(self, to):
        """sets the amount of time the solver is given for constructing a hypothesis"""
        self.timeout = to