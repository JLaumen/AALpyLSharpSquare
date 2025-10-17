from aalpy.oracles import BreadthFirstExplorationEqOracle
from itertools import product
from random import shuffle

class BFEOracle(BreadthFirstExplorationEqOracle):
    def __init__(self, alphabet, sul, depth=5):
        super().__init__(alphabet, sul, depth)
        self.queue = []

        # generate all test-cases
        for seq in product(self.alphabet, repeat=self.depth):
            self.queue.append(seq)

        shuffle(self.queue)
    def find_cex(self, hypothesis):

        while self.queue:
            test_case = self.queue.pop()
            self.reset_hyp_and_sul(hypothesis)

            for ind, letter in enumerate(test_case):
                out_hyp = hypothesis.step(letter)
                out_sul = self.sul.query(test_case[:ind+1])[-1]#self.sul.step(letter)
                self.num_steps += 1

                if out_hyp != out_sul:
                    self.sul.post()
                    return test_case[:ind + 1]

        return None
