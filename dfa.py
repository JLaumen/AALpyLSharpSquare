import z3
from dfa_builder import DFABuilder

def declsort_enum(name, elements):
    d = z3.DeclareSort(name)
    return d, [z3.Const(element, d) for element in elements]

class DFA:
    def __init__(self, labels, num_states, state_enum=declsort_enum, label_enum=declsort_enum):
        self.State, self.states = state_enum('State', ['state{0}'.format(i) for i in range(num_states)])
        self.start = self.states[0]
        labels = list(labels)
        self.Label, elements = label_enum('Label', labels)
        self.labels = {labels[i]: elements[i] for i in range(len(labels))}
        self.transition = z3.Function('transition', self.State, self.Label, self.State)
        self.output = z3.Function('output', self.State, z3.BoolSort())

    def export(self, model):
        builder = DFABuilder(self)
        dfa = builder.build_dfa(model)
        return dfa

