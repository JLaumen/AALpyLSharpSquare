from aalpy.base import Automaton
from aalpy.base import SUL

from random import random


class AutomatonSUL(SUL):
    def __init__(self, automaton: Automaton):
        super().__init__()
        self.automaton: Automaton = automaton

    def pre(self):
        self.automaton.reset_to_initial()

    def step(self, letter=None):
        return self.automaton.step(letter)

    def post(self):
        pass
    
class IncompleteAutomatonSUL(AutomatonSUL):
    def __init__(self, automaton: Automaton, setting, words:list=[], fractionKnown=0.5):
        super().__init__(automaton)
        assert setting in ["with", "without", "random"]
        self.setting = setting
        if setting == "with":
            self.withWords = words
        elif setting == "without":
            self.withoutWords = words
        else:
            self.withWords = []
            self.withoutWords = []
            self.fractionKnown = fractionKnown
    
    def pre(self):
        self.inputWalk = []
        self.automaton.reset_to_initial()

    def step(self, letter=None):
        self.inputWalk.append(letter)
        result = self.automaton.step(letter)
        if self.setting == "with":
            if self.inputWalk in self.withWords:
                return result
            else:
                return "unknown"
        elif self.setting == "without":
            if self.inputWalk in self.withoutWords:
                return "unknown"
            else:
                return result
        elif self.setting == "random":
            if self.inputWalk in self.withWords:
                return result
            elif self.inputWalk in self.withoutWords:
                return "unknown"
            else:
                if random() < self.fractionKnown:
                    self.withWords.append(self.inputWalk.copy())
                    return result
                else:
                    self.withoutWords.append(self.inputWalk.copy())
                    return "unknown"
        return result

    def post(self):
        pass

MealySUL = OnfsmSUL = StochasticMealySUL = DfaSUL = MooreSUL = MdpSUL = McSUL = SevpaSUL = AutomatonSUL
