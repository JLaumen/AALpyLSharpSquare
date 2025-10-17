from copy import deepcopy
from aalpy.learning_algs import run_RPNI
from aalpy.utils import make_input_complete

class RPNILearner:

    def __init__(self, dfa3, observation_table, description_type, early_detection):
        self.dfa3 = deepcopy(dfa3)
        self.observation_table = observation_table
        self.description_type = description_type
        self.early_detection = early_detection


    def learn(self):
        self.relabel_states()
        data_unlabeled = self.observation_table_to_data()
        data_unlabeled = set(data_unlabeled)
        data = []
        labels = []
        for word in data_unlabeled:
            label = self.dfa3.execute_sequence(self.dfa3.initial_state, word)
            if len(label) == 0:
                #data.append((word, False))
                if self.dfa3.initial_state.output != "?":
                    data.append((word, self.dfa3.initial_state.output == "+"))
            elif label[-1] != "?":
                data.append((word, label[-1] == "+"))
            labels.append(label)
        hypothesis = run_RPNI(data, automaton_type="dfa",print_info=False)
        # make_input_complete(hypothesis, 'sink_state')
        return hypothesis

    def observation_table_to_data(self):
        data = []
        for prefix in self.observation_table.T:
            labels = self.observation_table.T[prefix]
            for i, _ in enumerate(labels):
                data.append(prefix + self.observation_table.E[i])
        return data

    def relabel_states(self):
        for s in self.dfa3.states:
            s.sink_dont_care = False
            if s.output == "?":
                if all([x.state_id == s.state_id for x in s.transitions.values()]):
                    s.sink_dont_care = True
                    # print(f"Sink dont care state: {s.state_id}")

        if self.description_type == "RC":
            before = 0
            after = 0
            for s in self.dfa3.states:
                s.may_pass = False
                s.reject_before_sink = False
                if s.output == "-" and all([x.sink_dont_care for x in s.transitions.values()]): # or (x.state_id == s.state_id)
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
                    if s_id == s.state_id and all([x.state_id != s.state_id for x in s.transitions.values()]):
                        continue
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
        # print("3DFA after relabeling:")
        # print(self.dfa3)

    # old version
    # def relabel_states(self):
    #     # not similar to early detection (see end of this function)
    #     for s in self.dfa3.states:
    #         s.reach_reject = False
    #         s.reach_accept = False
    #     before = 0
    #     after = 0
    #     for s in self.dfa3.states:
    #         if s.output == "-":
    #             s.reach_reject = True
    #             after += 1
    #     while after != before:
    #         before = after
    #         for s in self.dfa3.states:
    #             for a, new_s in s.transitions.items():
    #                 if new_s.reach_reject and not s.reach_reject:
    #                     after += 1
    #                     s.reach_reject = True
    #     before = 0
    #     after = 0
    #     for s in self.dfa3.states:
    #         if s.output == "+":
    #             s.reach_accept = True
    #             after += 1
    #     while after != before:
    #         before = after
    #         for s in self.dfa3.states:
    #             for a, new_s in s.transitions.items():
    #                 if new_s.reach_accept and not s.reach_accept:
    #                     after += 1
    #                     s.reach_accept = True
    #     for s in self.dfa3.states:
    #         # if s.output == "?" and s.reach_accept and not s.reach_reject:
    #         #     s.output = "+"
    #         #based on Gal's comment
    #         if s.output == "?" and s.reach_reject:
    #             s.output = "-"