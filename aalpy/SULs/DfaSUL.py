from aalpy.base import Automaton
from aalpy.base.CacheTree import CacheTree
from aalpy.automata import Dfa
from aalpy.base import SUL

from random import random

class DfaSUL(SUL):
    def __init__(self, automaton: Dfa):
        super().__init__()
        self.automaton: Dfa = automaton
        self.num_unsuccesful_queries = 0

    def pre(self):
        self.automaton.reset_to_initial()
        self.last_output = self.automaton.step(None)

    def step(self, letter=None):
        self.last_output = self.automaton.step(letter)

    def post(self):
        return self.last_output
    
    def query(self, word: tuple) -> list:
        """
        Performs a membership query on the SUL. Before the query, pre() method is called and after the query post()
        method is called. Each letter in the word (input in the input sequence) is executed using the step method.

        Args:

            word: membership query (word consisting of letters/inputs)

        Returns:

            final output

        """
        self.pre()
        # Empty string for DFA
        for letter in word:
            self.step(letter)
        out = self.post()
        #print("query:", word, out)
        self.num_queries += 1
        self.num_steps += len(word)
        if out=="unknown":
            self.num_unsuccesful_queries += 1
        return out
    
class IncompleteDfaSUL(DfaSUL):
    
    def __init__(self, words:list=[()], automaton:Dfa=None, fractionKnown=0):
        super().__init__(automaton)
        self.cache = CacheTree()
        
        for word, output in words:
            self.add_word(word, output)
        for word, output in words:
            if self.word_known(word) != output:
                print(word, ":", output, "is known as", self.word_known(word))
        #self.words = words
        self.fractionKnown = fractionKnown
    
    def add_word(self, word, output):
        #print("add word", word, output)
        self.cache.reset()
        for index in range(len(word)):
            input_val = word[index]
            self.cache.step_in_cache(input_val)
        self.cache.step_in_cache(None, output)

    def word_known(self, word):
        outputs = self.cache.in_cache(word)
        if type(outputs) != list and type(outputs) != tuple:
            return outputs
        else:
            return outputs[-1]
        #print(word)
        #print(outputs)
        '''for word2, output2 in self.words:
            if word2 == word:
                return output2
        return None'''

    def pre(self):
        self.inputWalk = []
        if self.automaton is None:
            self.last_output = "unknown"
        else:
            self.automaton.reset_to_initial()
            self.last_output = self.automaton.step(None)

    def step(self, letter=None):
        self.inputWalk.append(letter)
        if self.automaton is None:
            self.last_output = "unknown"
        else:
            self.last_output = self.automaton.step(letter)

    def post(self):
        saved_output = self.word_known(self.inputWalk)
        if saved_output is None:
            if random() < self.fractionKnown and not self.automaton is None:
                #self.words.append((self.inputWalk.copy(), self.last_output))
                self.add_word(self.inputWalk, self.last_output)
                return self.last_output
            else:
                #self.words.append((self.inputWalk.copy(), "unknown"))
                self.add_word(self.inputWalk, "unknown")
                return "unknown"
        else:
            return saved_output
