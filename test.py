# Acceptor Test observations are tuples comprising sequences of Actions/Symbols joined by an accept/reject booleans
class Test:
    def __init__(self, trace):
        self.tr = trace

    def check(self, model):
        """checks if the hyp passes the test. On failure, it returns a minimal trace to be added by the learner.
        On success it return None"""
        # TODO this is a quick fix to the problem of not having a predefined alphabet from the very start.
        # if the trace contains new labels, then we return whole trace
        if len(self.input_labels().difference(model.input_labels())) != 0:
            return self.tr
        return self._check_trace(model, self.tr)

    def _check_trace(self, model, trace):
        (seq, acc) = trace
        if model.accepts(seq) != acc:
            return trace
        return None

    def size(self):
        (seq, acc) = self.tr
        return len(seq)

    def inputs(self):
        (seq, acc) = self.tr
        return seq

    def __hash__(self):
        (seq, acc) = self.tr
        return hash((type(self), frozenset(seq), acc))

    def __eq__(self, other):
        return other and type(other) is type(self) and other.tr == self.tr

    def __ne__(self, other):
        return not self.__eq__(other)

    def covers(self, test):
        if type(test) is type(self) and self.size() <= test.size():
            (seq, _) =  self.trace()
            (seq2, _) = test.trace()
            return seq == seq2
        return False

    def input_labels(self):
        """generates all the input labels in the test trace. Used to verify that model contains all test input labels"""
        inputs = self.inputs()
        input_labels = set()
        for inp in inputs:
            # if it's RA stuff
            if isinstance(inp, str):
                label = inp
            else:
                raise Exception("Unrecognized type")
            input_labels.add(label)

        return input_labels
