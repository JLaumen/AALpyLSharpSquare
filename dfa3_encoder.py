import z3
import itertools
from tree import Tree
from dfa import DFA
from mapper import Mapper


class DFA3Encoder:
    def __init__(self, dfa3, description_type, early_detection):  # description typeis one of ["FE", "RC"]
        self.dfa3 = dfa3
        self.labels = set([a for a in dfa3.get_input_alphabet()])
        for i, node in enumerate(dfa3.states):
            node.id = i
        self.description_type = description_type
        self.early_detection = early_detection
        self.label_states()

    def build(self, num_states, num_transitions_first, num_transitions_second):
        dfa = DFA(list(self.labels), num_states)
        mapper = Mapper(dfa)
        constraints = self.axioms(dfa, mapper)
        constraints += self.node_constraints(dfa, mapper)
        constraints += self.transition_constraints(dfa, mapper)
        if self.description_type:  # TODO: maybe add back
            constraints += self.suffix_closed_constraints(dfa, mapper)
            # constraints += self.rejecting_sink_constraints(dfa, mapper)
        constraints += self.first_transition_constraints(dfa, mapper, num_transitions_first)
        constraints += self.second_transition_constraints(dfa, mapper, num_transitions_second)
        return dfa, constraints

    def axioms(self, dfa, mapper):
        return [
            z3.And([z3.And([z3.Or([dfa.transition(state, label) == to_state
                                   for to_state in dfa.states]) for state in dfa.states])
                    for label in dfa.labels.values()]),
            z3.Distinct(list(dfa.labels.values())),
            z3.Distinct(list(dfa.states)),
            z3.Distinct([mapper.element(node.id) for node in self.dfa3.states if not node.sink_dont_care]),
           # z3.And([z3.Or([mapper.map(mapper.element(node.id)) == q for node in self.cache]) for q in dfa.states])
        ]

    def node_constraints(self, dfa, mapper):
        constraints = []
        for node in self.dfa3.states:
            if node.output == "?":
                continue
            accept = node.output == "+"
            n = mapper.element(node.id)
            constraints.append(dfa.output(mapper.map(n)) == accept)
        return constraints

    def transition_constraints(self, dfa, mapper):
        constraints = [dfa.start == mapper.map(mapper.start)]
        for node in self.dfa3.states:
            # print(node.state_id, mapper.element(node.id))
            for label, child in node.transitions.items():
                if child.sink_dont_care:
                    continue
                n = mapper.element(node.id)
                l = dfa.labels[label]
                c = mapper.element(child.id)
                constraints.append(dfa.transition(mapper.map(n), l) == mapper.map(c))
                # print(dfa.transition(mapper.map(n), l) == mapper.map(c))
        # print(len(constraints))
        # print(constraints[1])
        return constraints

    def suffix_closed_constraints(self, dfa, mapper):
        return [z3.And([z3.And([z3.Implies(dfa.output(state), dfa.output(dfa.transition(state, label))) for state in dfa.states]) for label in dfa.labels.values()])]

    def rejecting_sink_constraints(self, dfa, mapper):
        return [z3.And([z3.Not(dfa.output(dfa.states[-1]))] + [dfa.transition(dfa.states[-1], label) == dfa.states[-1] for label in dfa.labels.values()])]

    def first_transition_constraints(self, dfa, mapper, num_transitions):
        return [z3.Sum([z3.If(dfa.transition(state, label) == dfa.states[-1], 0, 1) for state in dfa.states for label in dfa.labels.values()]) <= num_transitions]

    def second_transition_constraints(self, dfa, mapper, num_transitions):
        return [z3.Sum([z3.If(dfa.transition(state, label) == state, 0, 1) for state in dfa.states for label in dfa.labels.values()]) <= num_transitions]

    def label_states(self):
        for s in self.dfa3.states:
            s.sink_dont_care = False
            if s.output == "?":
                if all([x.state_id == s.state_id for x in s.transitions.values()]):
                    s.sink_dont_care = True
                    print(f"Sink dont care state: {s.state_id}")

        if self.description_type == "RC":
            before = 0
            after = 0
            for s in self.dfa3.states:
                s.may_pass = False
                s.reject_before_sink = False
                if s.output == "-" and all([x.sink_dont_care for x in s.transitions.values()]):
                    s.reject_before_sink = True
                    s.may_pass = True
                    after += 1
            while after != before:
                before = after
                for s in self.dfa3.states:
                    for a, new_s in s.transitions.items():
                        if new_s.may_pass and not s.may_pass:
                            after += 1
                            s.may_pass = True

            connected_components = [{s.state_id} for s in self.dfa3.states]
            for i, s1 in enumerate(self.dfa3.states):
                for j, s2 in enumerate(self.dfa3.states[i+1:]):
                    if (self.dfa3.get_shortest_path(s1, s2) is not None) and (self.dfa3.get_shortest_path(s2, s1) is not None):
                        new_item = [x for x in connected_components if s1.state_id in x][0] | [x for x in connected_components if s2.state_id in x][0]
                        connected_components = [x for x in connected_components if s1.state_id not in x and s2.state_id not in x]
                        connected_components.append(new_item)
            before = 0
            after = 0
            for s in self.dfa3.states:
                if s.may_pass:
                    continue
                component = [x for x in connected_components if s.state_id in x][0]
                for s_id in component:
                    s2 = [x for x in self.dfa3.states if x.state_id == s_id][0]
                    if s2.output == "-":
                        s.may_pass = True
                        after += 1
            while after != before:
                before = after
                for s in self.dfa3.states:
                    for a, new_s in s.transitions.items():
                        if new_s.may_pass and not s.may_pass:
                            after += 1
                            s.may_pass = True

            for s in self.dfa3.states:
                if s.output == "-" and not s.may_pass:
                    s.output = "?"  # by definition3 in overleaf



        if self.early_detection:
            for s in self.dfa3.states:
                s.reach_reject = False
                s.reach_accept = False
            before = 0
            after = 0
            for s in self.dfa3.states:
                if s.output == "-":
                    s.reach_reject = True
                    after += 1
            while after != before:
                before = after
                for s in self.dfa3.states:
                    for a, new_s in s.transitions.items():
                        if new_s.reach_reject and not s.reach_reject:
                            after += 1
                            s.reach_reject = True
            before = 0
            after = 0
            for s in self.dfa3.states:
                if s.output == "+":
                    s.reach_accept = True
                    after += 1
            while after != before:
                before = after
                for s in self.dfa3.states:
                    for a, new_s in s.transitions.items():
                        if new_s.reach_accept and not s.reach_accept:
                            after += 1
                            s.reach_accept = True
            for s in self.dfa3.states:
                if s.output == "?" and s.reach_accept and not s.reach_reject:
                    s.output = "+"
                if s.output == "?" and s.reach_reject and not s.reach_accept:
                    s.output = "-"
        print("3DFA after relabeling:")
        print(self.dfa3)
