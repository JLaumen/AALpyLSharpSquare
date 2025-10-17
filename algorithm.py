from typing import cast
import time
from test import Test
from aalpy.automata import Dfa, DfaState


def dfa_transform(automaton, remove_sink_state=True):
    mapper = {}
    init = None
    for s in automaton.states():
        mapper[s] = DfaState(s, is_accepting=automaton.is_accepting(s))
        if automaton.start_state() == s:
            init = mapper[s]
    for s in automaton.states():
        for a in automaton.input_labels():
            mapper[s].transitions[a] = mapper[automaton.transitions(s, a)[0].end_state]
    final = Dfa(init, list(mapper.values()))
    if remove_sink_state:
        for s in final.states:
            if not s.is_accepting:
                is_sink = all([x == s for x in s.transitions.values()])
                if is_sink:
                    for s1 in final.states:
                        for a in list(s1.transitions.keys()):
                            if s1.transitions[a] == s:
                                s1.transitions.pop(a)
                    final.states.remove(s)
        return final
    else:
        return final



class Statistics():
    """We only refe"""
    def __init__(self):
        self.learning_times = []
        self.model_stats = None
        self.resets = 0
        self.inputs = 0

    def add_learning_time(self, time):
        self.learning_times.append(time)

    def set_num_resets(self, test_num):
        self.resets = test_num

    def set_num_inputs(self, inp_num):
        self.inputs = inp_num

    def __str__(self):        return \
        "Tests until last hyp: {} \n" \
        "Inputs until last hyp: {} \n " \
        "Hypotheses used in learning: {} \n " \
        "Learning time for each model: {} \n " \
        "Total learning time: {} ".format(        self.resets,
                                                  self.inputs,
                                                   len(self.learning_times),
                                                  self.learning_times,
                                                   sum(self.learning_times))


def learn(learner, traces):
    """ takes learner and a list of traces and generates a model"""
    statistics = Statistics()
    if len(traces) < 0:
        return (None, statistics)
    else:
        if learner.use_all_traces:
            learn_traces = []
            model = None
            definition = None
            for trace in traces:
                test = Test(trace)
                learner.add(test.tr)
                learn_traces.append(test.tr)
            start_time = int(time.time() * 1000)
            while True:
                (model, definition) = learner.model(old_definition=definition)
                # print(model)
                dfa = dfa_transform(model, remove_sink_state=False)
                cex = learner.oracle.find_cex(dfa)
                if cex is None:
                    break
                else:
                    if len(cex) == 0:
                        test = Test((cex, not dfa.initial_state.is_accepting))
                    else:
                        test = Test((cex, not dfa.execute_sequence(dfa.initial_state, cex)[-1]))
                    #print("CE: ", test.tr)
                    learner.add(test.tr)
                    learn_traces.append(test.tr)
            end_time = int(time.time() * 1000)
            statistics.add_learning_time(end_time - start_time)
            done = True
            return dfa_transform(model, remove_sink_state=False), statistics
        else:
            test = Test(traces.pop(0))
            definition = None
            learner.add(test.tr)
            done = False
            model = None
            learn_traces = [test.tr]
            while not done:
                start_time = int(time.time() * 1000)
                (model, definition) = learner.model(old_definition=definition)
                end_time = int(time.time() * 1000)
                statistics.add_learning_time(end_time - start_time)
                done = True
                for trace in traces:
                    test = Test(trace)
                    ce = test.check(model)
                    if ce is not None:
                        if ce not in learn_traces:
                            learn_traces.append(ce)
                        else:
                            raise Exception("The CE {0} has already been processed yet it "
                                            "is still a CE. \n CEs: {1} \n Model: {2}".format(ce, learn_traces, model))
                        print("CE: ", ce)
                        learner.add(ce)
                        done = False
                        break
                if not done:
                    traces.remove(ce)
            return (model, statistics)
