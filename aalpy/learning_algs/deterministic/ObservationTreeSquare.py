import datetime
import itertools
import logging
import time
from collections import deque

from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import (
    Solver, Symbol, Function, Int, Bool, Or, GE, LT
)
from pysmt.typing import INT, BOOL, FunctionType

from .Apartness import Apartness
from .Nodes import MooreNode
from ... import Dfa, DfaState

# timeout = 60000
timeout = 3600 * 1000

test_cases_path = "Benchmarking/incomplete_dfa_benchmark/test_cases/"
logging.basicConfig(level=logging.INFO,
                    format=f"%(asctime)s %(levelname)s: %(message)s",
                    datefmt="%H:%M:%S")


class ObservationTreeSquare:
    def __init__(self, alphabet, sul):
        """
        Initializes the observation tree with a root node.
        """
        self.automaton_type = "dfa"

        # Logger information
        self.smt_time = 0
        MooreNode._id_counter = 0

        # Initialize tree
        self.alphabet = alphabet
        self.sul = sul
        self.outputAlphabet = [True, False, "unknown"]
        self.states_list = []

        self.root = MooreNode()
        self.root.set_output(self.sul.query([]))

        self.size = 1
        self.guaranteed_basis = [self.root]
        self.frontier_to_basis_dict = dict()

        self.apartness_cache = set()

    def insert_observation(self, inputs, output):
        """
        Insert an observation into the tree using a sequence of inputs and the corresponding output.
        """
        node = self.root
        for inp in inputs:
            node = node.extend_and_get(inp, None)
        node.set_output(output)

    def insert_observation_sequence(self, inputs, outputs):
        """
        Insert an observation into the tree using a sequence of inputs and their corresponding outputs.
        """
        # print("Insert observation sequence:", inputs, outputs)
        node = self.root
        for inp, output in zip(inputs, outputs):
            node = node.extend_and_get(inp, [output[-1]])
            node.set_output([output[-1]])
            if not node in self.frontier_to_basis_dict:
                candidates = {candidate for candidate in self.guaranteed_basis if
                              not Apartness.states_are_incompatible(candidate, node, self)}
                self.frontier_to_basis_dict[node] = candidates

    def experiment(self, inputs):
        """
        Perform an experiment by querying the SUL if necessary and updating the tree.
        """
        node = self.get_successor(inputs)
        if node is None or node.output is None:
            output = self.sul.query(inputs)
            self.insert_observation(inputs, output)
            return output
        return node.output

    def get_successor(self, inputs, start_node=None):
        """
        Retrieve the node corresponding to the given input sequence
        """
        if start_node is None:
            node = self.root
        else:
            node = start_node
        for input_val in inputs:
            successor_node = node.get_successor(input_val)
            if successor_node is None:
                return None
            node = successor_node
        return node

    @staticmethod
    def get_transfer_sequence(start_node, end_node):
        """
        Get the sequence of inputs that moves from the start node to the end node.
        """
        transfer_sequence = []
        node = end_node

        while node != start_node:
            if node.parent is None:
                return None
            transfer_sequence.append(node.input_to_parent)
            node = node.parent

        transfer_sequence.reverse()
        return transfer_sequence

    def get_access_sequence(self, target_node):
        """
        Get the sequence of inputs that moves from the root node to the target node.
        """
        transfer_sequence = []
        node = target_node

        while node != self.root:
            if node.parent is None:
                return None
            transfer_sequence.append(node.input_to_parent)
            node = node.parent

        transfer_sequence.reverse()
        return transfer_sequence

    def get_size(self):
        """
        Get the number of nodes in the observation tree.
        """
        return self.root.id_counter

    @staticmethod
    def is_known(node):
        """
        Check if the output of a node is known.
        """
        return node.output is not None and node.output != ['?']

    def count_informative_nodes(self):
        """
        counts how many nodes have informative information
        """
        queue = deque()
        queue.append(self.root)
        count = 0
        while queue:
            node = queue.popleft()
            if self.is_known(node):
                count += 1
            for successor in node.successors.values():
                queue.append(successor)
        return count

    def update_basis_candidates(self, frontier_node):
        """
        Update the basis candidates for a specific frontier node.
        """
        candidates = self.frontier_to_basis_dict[frontier_node]
        new_candidates = {node for node in candidates if
                          not Apartness.states_are_incompatible(frontier_node, node, self)}
        self.frontier_to_basis_dict[frontier_node] = new_candidates

    def update_frontier_to_basis_dict(self):
        """
        Update the basis candidates for all frontier nodes.
        """
        self.update_frontier_to_basis_dict_dfs(self.root)

    def update_frontier_to_basis_dict_dfs(self, node):
        if not node.leads_to_known:
            return
        if not node in self.guaranteed_basis:
            self.update_basis_candidates(node)
        for successor in node.successors.values():
            self.update_frontier_to_basis_dict_dfs(successor)

    def promote_node_to_basis(self):
        """
        If an isolated frontier node is found, reset the queue and restart from the guaranteed basis plus the isolated node.
        """
        for iso_frontier_node, basis_list in self.frontier_to_basis_dict.items():
            if not basis_list:
                self.guaranteed_basis.append(iso_frontier_node)
                # Update the candidates
                del self.frontier_to_basis_dict[iso_frontier_node]
                for node, candidates in self.frontier_to_basis_dict.items():
                    if not Apartness.states_are_incompatible(node, iso_frontier_node, self):
                        candidates.add(iso_frontier_node)
                self.size = max(self.size, len(self.guaranteed_basis))
                return True
        return False

    def make_frontiers_identified(self):
        """
        Loop over all frontier nodes to identify them
        """
        extended = False
        for basis_node in self.guaranteed_basis:
            for letter in self.alphabet:
                frontier_node = basis_node.get_successor(letter)
                if self.identify_frontier(frontier_node):
                    extended = True
        return extended

    def identify_frontier(self, frontier_node):
        """
        Identify a specific frontier node
        """
        if len(self.frontier_to_basis_dict[frontier_node]) <= 1:
            return False

        inputs_to_frontier = self.get_transfer_sequence(self.root, frontier_node)

        out_extended = False
        witnesses = self._get_witnesses_bfs(frontier_node)
        for witness_seq in witnesses:
            inputs = inputs_to_frontier + witness_seq
            outputs, extended = self._get_output_sequence(inputs, query_mode='final')
            if extended:
                out_extended = True
            self.insert_observation_sequence(inputs, outputs)
        return out_extended

    def _get_witnesses_bfs(self, frontier_node):
        """
        Specifically identify frontier nodes using separating sequences
        """
        basis_candidates = self.frontier_to_basis_dict.get(frontier_node)
        witnesses = Apartness.get_distinguishing_sequences(basis_candidates, self)

        for witness_seq in witnesses:
            leads_to_node = self.get_successor(witness_seq, start_node=frontier_node)
            if leads_to_node is None or leads_to_node.output is None:
                yield witness_seq

    def construct_hypothesis_states(self, output_mapping=None):
        """
        Construct the hypothesis states from the basis
        """
        self.states_list = [DfaState(f's{i}') for i in range(self.size)]
        for i, dfa_state in enumerate(self.states_list):
            dfa_state.is_accepting = output_mapping[i]

    def construct_hypothesis_transitions(self, transition_mapping=None):
        """
        Construct the hypothesis transitions using the transition_mapping and output_mapping.
        """
        for i, dfa_state in enumerate(self.states_list):
            for j, letter in enumerate(self.alphabet):
                dfa_state.transitions[letter] = self.states_list[transition_mapping[i][j]]

    def construct_hypothesis(self, transition_mapping=None, output_mapping=None):
        """
        Constructs the hypothesis DFA from the transition and output mappings.
        """
        self.construct_hypothesis_states(output_mapping=output_mapping)
        self.construct_hypothesis_transitions(transition_mapping=transition_mapping)

        hypothesis = Dfa(self.states_list[0], self.states_list)
        hypothesis.compute_prefixes()
        hypothesis.characterization_set = hypothesis.compute_characterization_set(raise_warning=False)

        return hypothesis

    def find_hypothesis(self):
        """
        Find a hypothesis consistent with the observation tree, using the pySMT solver.
        There are 2 free functions: "out" and "m" and 1 bound function "delta".
        """
        print("Building hypothesis of size", self.size)
        print("Basis size:", len(self.guaranteed_basis), "Frontier size:", len(self.frontier_to_basis_dict))
        logging.debug(f"Trying to build hypothesis of size {self.size}")
        logging.debug(f"Basis size: {len(self.guaranteed_basis)}, Frontier size: {len(self.frontier_to_basis_dict)}")
        start_smt_time = time.time()

        s = Solver(name="z3", solver_options={"timeout": timeout})  # or another backend supported by pySMT

        # Function declarations
        delta = Symbol("delta", FunctionType(INT, [INT, INT]))  # δ: int × int → int
        dfa_output = Symbol("dfa_output", FunctionType(BOOL, [INT]))  # dfa_output: int → bool
        states_mapping = Symbol("states_mapping", FunctionType(INT, [INT]))  # states_mapping: int → int

        # Flatten the tree to a list of nodes
        queue = deque([self.root])
        nodes = [self.root]

        while queue:
            node = queue.popleft()
            idx = nodes.index(node)
            for letter, successor in node.successors.items():
                # Check if successor can reach a known node
                if not successor.leads_to_known:
                    continue
                queue.append(successor)
                s.add_assertion(
                    Function(states_mapping, [Int(len(nodes))]).Equals(
                        Function(delta, [Function(states_mapping, [Int(idx)]), Int(self.alphabet.index(letter))]))
                )
                nodes.append(successor)

        # Basis nodes map to different states
        for i, node in enumerate(self.guaranteed_basis):
            s.add_assertion(Function(states_mapping, [Int(nodes.index(node))]).Equals(Int(i)))
            # break

        # Force known outputs
        for i, node in enumerate(nodes):
            if self.is_known(node):
                # raise ValueError(f"{node.output}")
                b = None
                if node.output[0] == "+":
                    b = True
                elif node.output[0] == "-":
                    b = False
                else:
                    raise ValueError(f"Unknown output {node.output} in SMT encoding.")
                val = Bool(b)
                s.add_assertion(Function(dfa_output, [Function(states_mapping, [Int(i)])]).Iff(val))

        for node, candidates in self.frontier_to_basis_dict.items():
            # break
            if node not in nodes:
                continue
            s.add_assertion(Or([
                                   Function(states_mapping, [Int(nodes.index(node))]).Equals(
                                       Int(self.guaranteed_basis.index(c))) for c in candidates] +
                               [Function(states_mapping, [Int(nodes.index(node))]).Equals(Int(i)) for i in
                                range(len(self.guaranteed_basis), self.size)]))

        # Correct delta
        for i in range(self.size):
            for j in range(len(self.alphabet)):
                d_ij = Function(delta, [Int(i), Int(j)])
                s.add_assertion(GE(d_ij, Int(0)))
                s.add_assertion(LT(d_ij, Int(self.size)))

        # Fix known delta transitions for basis to basis nodes
        # for i, node in enumerate(self.basis):
        #     for letter, successor in node.successors.items():
        #         if successor in self.basis:
        #             s.add_assertion(
        #                 Function(delta, [Int(i), Int(self.alphabet.index(letter))]) \
        #                     .Equals(Int(self.basis.index(successor)))
        #             )

        try:
            logging.debug("Solving...")
            if not s.solve():
                logging.debug("UNSAT")
                logging.debug(f"No hypothesis of size {self.size} exists")
                self.smt_time += time.time() - start_smt_time
                return None, None
            else:
                logging.debug("SAT")
                self.smt_time += time.time() - start_smt_time
                model = s.get_model()

                transition_mapping = [[0 for _ in range(len(self.alphabet))] for _ in range(self.size)]
                output_mapping = [False for _ in range(self.size)]

                for i in range(self.size):
                    val = model.get_value(Function(dfa_output, [Int(i)]))
                    output_mapping[i] = str(val) == "True"
                    for j in range(len(self.alphabet)):
                        val = model.get_value(Function(delta, [Int(i), Int(j)]))
                        transition_mapping[i][j] = int(str(val))

                return transition_mapping, output_mapping
        except SolverReturnedUnknownResultError:
            self.smt_time += time.time() - start_smt_time
            logging.debug("TIMEOUT")
            logging.debug(f"Could not find hypothesis of size {self.size}")
            return None, None

    def build_hypothesis(self):
        """
        Builds the hypothesis which will be sent to the SUL and checks consistency
        """
        while True:
            self.find_adequate_observation_tree()
            transition_mapping, output_mapping = self.find_hypothesis()
            if transition_mapping is not None:
                hypothesis = self.construct_hypothesis(transition_mapping=transition_mapping,
                                                       output_mapping=output_mapping)
                return hypothesis
            else:
                self.size += 1
                return None

    def expand_frontier(self):
        """
        Extend the frontier self.size - len(self.guaranteed_basis) steps from the guaranteed basis
        """
        length = self.size - len(self.guaranteed_basis) + 1
        # length = 1
        # Loop over words of length 'length'
        for word in itertools.product(self.alphabet, repeat=length):
            for node in self.guaranteed_basis:
                access = self.get_access_sequence(node)
                inputs = access + list(word)
                outputs, _ = self._get_output_sequence(inputs, query_mode="full")
                self.insert_observation_sequence(inputs, outputs)

    def update_frontier(self):
        # self.extend_frontier()
        self.update_frontier_to_basis_dict()

    def find_adequate_observation_tree(self):
        """
        Tries to find an observation tree, 
        for which each frontier state is identified as much as possible.
        """
        self.update_frontier()
        self.expand_frontier()
        while self.promote_node_to_basis():
            self.update_frontier()
            self.expand_frontier()

        while self.make_frontiers_identified():
            self.update_frontier_to_basis_dict()
            while self.promote_node_to_basis():
                self.update_frontier()
                self.expand_frontier()

    def process_counter_example(self, cex_inputs, cex_outputs):
        """
        Inserts the counter example into the observation tree and searches for the
        input-output sequence which is different
        """
        print("Processing counterexample:", cex_inputs, cex_outputs)
        cex_outputs, _ = self._get_output_sequence(cex_inputs, query_mode="full")
        self.insert_observation_sequence(cex_inputs, cex_outputs)


    def _get_output_sequence(self, inputs, query_mode="full"):
        """ 
        Returns the sequence of outputs corresponding to the input path. 
        The knowledge is obtained from the observation tree or if not available via querying the sul. 
        There are 3 query_modes: full, none and final. They allow you to restrict the querying to your needs
        """
        assert query_mode in ["full", "none", "final"]

        outputs = []
        queried = False
        current_node = self.root
        for inp_num in range(len(inputs)):
            inp = inputs[inp_num]
            if current_node is not None:
                current_node = current_node.get_successor(inp)
            if current_node is None:
                if query_mode == "full" or (inp_num == len(inputs) - 1 and query_mode == "final"):
                    outputs.append(self.sul.query(inputs[:inp_num + 1]))
                    queried = True
                else:
                    outputs.append(None)
            else:
                if current_node.output is None and (
                        query_mode == "full" or (inp_num == len(inputs) - 1 and query_mode == "final")):
                    outputs.append(self.sul.query(inputs[:inp_num + 1]))
                    queried = True
                else:
                    outputs.append(current_node.output)
        return outputs, queried
