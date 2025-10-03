import itertools
import time
from collections import deque
# from .ADS import Ads
from .Apartness import Apartness
from ... import Dfa, DfaState, MealyState, MealyMachine, MooreMachine, MooreState
from .Nodes import MooreNode
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.shortcuts import (
    Solver, Symbol, Function, Int, Bool, Or, GE, LT, get_env
)
from pysmt.typing import INT, BOOL, FunctionType

# Supported automata types
aut_type = ['dfa']


class ObservationTreeSquare:
    def __init__(self, alphabet, sul, automaton_type):
        """
        Initializes the observation tree with a root node.
        """
        assert automaton_type in aut_type
        assert alphabet is not None and sul is not None

        # Logger information
        self.queries = 0
        self.smt_time = 0
        self.rule1_applications = 0
        self.rule2_applications = 0
        self.rule3_applications = 0
        self.rule4_applications = 0
        self.bases_analyzed = 1
        MooreNode._id_counter = 0

        # Initialize tree
        self.alphabet = alphabet
        self.sul = sul
        self.automaton_type = automaton_type
        self.outputAlphabet = [True, False, "unknown"]

        self.root = MooreNode()
        self.root.output = self.sul.query([])

        self.size = 1
        self.guaranteed_basis = [self.root]
        self.frontier_to_basis_dict = dict()

        self.apartness_cache = set()

    def insert_observation(self, inputs, output):
        """
        Insert an observation into the tree using a sequence of inputs and the corresponding output.
        """
        node = self.root
        for input in inputs:
            node = node.extend_and_get(input, None)
        node.output = output

    def insert_observation_sequence(self, inputs, outputs):
        """
        Insert an observation into the tree using a sequence of inputs and their corresponding outputs.
        """
        # if len(inputs) != len(outputs):
        #     raise ValueError("Inputs and outputs must have the same length.")

        node = self.root
        for input, output in zip(inputs, outputs):
            node = node.extend_and_get(input, output)
            node.output = output
            if not node in self.frontier_to_basis_dict:
                candidates = {candidate for candidate in self.guaranteed_basis if not Apartness.states_are_incompatible(candidate, node, self)}
                self.frontier_to_basis_dict[node] = candidates

    def get_observations(self, inputs):
        """
        Retrieve the list of outputs based on a given sequence of inputs.
        """
        node = self.root
        observations = []
        for input in inputs:
            node = node.get_successor(input)
            output = node.output
            observations.append(output)
        return observations

    # def get_outputs(self, start_node, inputs):
    #     """
    #     Retrieve the list of outputs based on a given sequence of inputs, starting from a specific node.
    #     """
    #     prefix = self.get_transfer_sequence(self.root, start_node)
    #     node = self.get_successor(prefix)
    #     observations = []
    #     for input_val in inputs:
    #         output = node.output
    #         observations.append(output)
    #         node = node.get_successor(input_val)
    #     return observations

    def experiment(self, inputs):
        """
        Perform an experiment by querying the SUL if necessary and updating the tree.
        """
        node = self.get_successor(inputs)
        if node is None or node.output is None:
            # Query the SUL
            # self.queries += 1
            output = self.sul.query(inputs)
            # print(self.queries)
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
        return node.output is not None and node.output != "unknown"

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

    # Functions related to finding new basis and frontier nodes
    def update_frontier_and_basis(self):
        """
        Updates the frontier to basis map, promotes a frontier node and checks for consistency
        """
        self.update_frontier_to_basis_dict()
        self.promote_frontier_node_in_queue_reset()
        self.extend_frontier()
        self.update_frontier_to_basis_dict()

    def update_basis_candidates(self, frontier_node):
        """
        Update the basis candidates for a specific frontier node.
        """
        # if frontier_node not in self.frontier_to_basis_dict:
        #     raise RuntimeError(f"Node not in frontier")

        candidates = self.frontier_to_basis_dict[frontier_node]
        new_candidates = {node for node in candidates if
                          not Apartness.states_are_incompatible(frontier_node, node, self)}
        self.frontier_to_basis_dict[frontier_node] = new_candidates

    def update_frontier_to_basis_dict(self):
        """
        Update the basis candidates for all frontier nodes.
        """
        for node in self.frontier_to_basis_dict:
            self.update_basis_candidates(node)
        # for node, candidates in list(self.frontier_to_basis_dict.items()):
        #     if len(candidates) == 1 and list(candidates)[0] in self.guaranteed_basis and list(candidates)[0].parent is not None and list(candidates)[0].parent not in self.basis:
        #         print(f"Foreigner member {list(candidates)[0].id} can be added to normal basis")

    def add_frontier_to_queue(self, new_basis_node):
        """
        Add the current basis to the queue, extended with a new basis node.
        """
        new_basis = self.basis + [new_basis_node]
        new_frontier_to_basis_dict = {node: candidates.union({new_basis_node}) for node, candidates in
                                      self.frontier_to_basis_dict.items()}
        del new_frontier_to_basis_dict[new_basis_node]
        self.queue.append((new_basis, new_frontier_to_basis_dict))

    def promote_frontier_node_in_queue(self):
        """
        checks the queue, if there is an isolated frontier node, 
        it combines the current basis with the isolated frontier node, 
        and adds this to the queue
        """
        for iso_frontier_node, basis_list in self.frontier_to_basis_dict.items():
            if not basis_list:
                new_basis = iso_frontier_node
                self.basis.append(new_basis)
                del self.frontier_to_basis_dict[new_basis]
                for frontier_node, new_basis_list in self.frontier_to_basis_dict.items():
                    if not Apartness.states_are_incompatible(new_basis, frontier_node, self):
                        new_basis_list.append(new_basis)
                already_in_queue = False
                for basis2, _ in self.queue:
                    if set(basis2) == set(self.basis):
                        already_in_queue = True
                if not already_in_queue:
                    self.queue.append((self.basis, self.frontier_to_basis_dict))
                self.basis, self.frontier_to_basis_dict = self.queue.popleft()
                self.bases_analyzed += 1
                self.rule1_applications += 1
                break

    def promote_frontier_node_in_queue_reset(self):
        """
        If an isolated frontier node is found, reset the queue and restart from the guaranteed basis plus the isolated node.
        """
        for iso_frontier_node, basis_list in self.frontier_to_basis_dict.items():
            if not basis_list:
                # print(f"Promoting isolated frontier node {iso_frontier_node.id} to basis")
                # if iso_frontier_node.parent not in self.guaranteed_basis:
                #     print("Foreign member")
                # if not basis_list:
                # New basis: guaranteed basis + isolated node (preserving order)
                self.guaranteed_basis.append(iso_frontier_node)
                # Update the frontier
                new_frontier_to_basis_dict = {node: set(self.guaranteed_basis) for node, candidates in
                                              self.frontier_to_basis_dict.items() if
                                              node not in self.guaranteed_basis}
                self.frontier_to_basis_dict = new_frontier_to_basis_dict
                self.bases_analyzed += 1
                if len(self.guaranteed_basis) > self.size:
                    self.size = len(self.guaranteed_basis)
                return True
        return False
        # elif not set(basis_list).intersection(set(self.guaranteed_basis)):
        #     print("Warning: Isolated frontier node found but not promoted due to existing basis nodes outside guaranteed basis.")

    def extend_frontier(self):
        """
        Check if all successors of all basis nodes is fully defined in the frontier.
        """
        extended = False
        for basis_node in self.basis:
            for letter in self.alphabet:
                successor = basis_node.get_successor(letter)
                if successor in self.basis:
                    continue
                if successor is None or successor.output is None:
                    extended = True
                    # Query the SUL
                    # self.queries += 1
                    output = self.sul.query(self.get_access_sequence(basis_node) + [letter])
                    # print(self.queries)
                    if successor is None:
                        successor = basis_node.extend_and_get(letter, output)
                    else:
                        successor.output = output
                if successor not in self.frontier_to_basis_dict:
                    candidates = set(self.basis)
                    self.frontier_to_basis_dict[successor] = candidates
        return extended
        # for basis_node in self.basis:
        #     for i in self.alphabet:
        #         maybe_frontier = basis_node.get_successor(i)

        #         if maybe_frontier is None:
        #             self.explore_frontier(basis_node, i)
        #             self.rule2_applications += 1
        #             maybe_frontier = basis_node.get_successor(i)

        #         if (self.automaton_type == 'moore' or self.automaton_type == 'dfa') and maybe_frontier.output is None:
        #             inputs = self.get_transfer_sequence(self.root, maybe_frontier)
        #             outputs = self._get_output_sequence(inputs, query_mode="full")
        #             self.insert_observation_sequence(inputs, outputs)
        #             assert maybe_frontier.output is not None

        #         if maybe_frontier in self.basis or maybe_frontier in self.frontier_to_basis_dict:
        #             continue

        #         self.frontier_to_basis_dict[maybe_frontier] = [
        #             new_basis_node for new_basis_node in self.basis
        #             if not Apartness.states_are_incompatible(new_basis_node, maybe_frontier, self)
        #         ]

    def is_observation_tree_adequate(self):
        """
        Check for each frontier node if they have only 1 basis candidate, 
        or have multiple candidates but no more witnesses to narrow it down. 
        Also check if all basis nodes have some output for every input.
        """
        for frontier_node, basis_list in self.frontier_to_basis_dict.items():
            if len(basis_list) != 1:
                if len(basis_list) > 1:
                    distinguishing_sequences = Apartness._get_distinguishing_sequences_moore(basis_list,
                                                                                             self.alphabet)
                    for distinguishing_sequence in distinguishing_sequences:
                        inputs = list(self.get_access_sequence(frontier_node)) + distinguishing_sequence
                        distinguishingNode = self.get_successor(inputs)
                        if distinguishingNode is not None and (
                                distinguishingNode.output != "unknown" and distinguishingNode.output is not None):
                            return False
                else:
                    return False

        for basis_node in self.basis:
            for inp in self.alphabet:
                if self.automaton_type == 'mealy':
                    if basis_node.get_output(inp) is None:
                        return False
                else:
                    if basis_node.get_successor(inp) is None or basis_node.output is None:
                        return False

        return True

    def make_frontier_complete(self):
        """
        Explore new frontier nodes and add them to the frontier_to_basis_dict, if they are new.
        """
        for basis_node in self.basis:
            for inp in self.alphabet:
                if basis_node.get_successor(inp) is None:
                    self.explore_frontier(basis_node, inp)
                    new_frontier = basis_node.get_successor(inp)
                    basis_candidates = self.find_basis_candidates(new_frontier)
                    self.frontier_to_basis_dict[new_frontier] = basis_candidates

    def find_basis_candidates(self, new_frontier):
        return {
            new_basis_node for new_basis_node in self.basis
            if not Apartness.states_are_incompatible(new_basis_node, new_frontier, self)
        }

    def explore_frontier(self, basis_node, inp):
        """
        Explores a specific frontier node (basis node + input) by passing a query to the SUL
        """
        inputs = self.get_transfer_sequence(self.root, basis_node) + [inp]
        outputs, _ = self._get_output_sequence(inputs)
        self.insert_observation_sequence(inputs, outputs)

    def make_frontiers_identified(self):
        """
        Loop over all frontier nodes to identify them
        """
        extended = False
        # frontier_dict = self.frontier_to_basis_dict.copy()
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
            # print(witness_seq)
            self.rule3_applications += 1

            inputs = inputs_to_frontier + witness_seq
            outputs, extended = self._get_output_sequence(inputs, query_mode='final')
            if extended:
                out_extended = True
            self.insert_observation_sequence(inputs, outputs)
            # if outputs[-1] != "unknown":
            #     break

        return out_extended

    def _get_witnesses_bfs(self, frontier_node):
        """
        Specifically identify frontier nodes using separating sequences
        """
        basis_candidates = self.frontier_to_basis_dict.get(frontier_node)
        witnesses = Apartness._get_distinguishing_sequences(basis_candidates, self)

        for witness_seq in witnesses:
            leads_to_node = self.get_successor(witness_seq, start_node=frontier_node)
            if leads_to_node is None or leads_to_node.output is None:
                yield witness_seq

    def construct_hypothesis_states(self, output_mapping=None):
        """
        Construct the hypothesis states from the basis
        """
        self.states_dict = [None for _ in range(self.size)]

        for i in range(self.size):
            self.states_dict[i] = DfaState(f's{i}')
            self.states_dict[i].is_accepting = output_mapping[i]

    def construct_hypothesis_transitions(self, transition_mapping=None, output_mapping=None):
        """
        Construct the hypothesis transitions using the transition_mapping and output_mapping.
        """
        for i in range(self.size):
            for j, letter in enumerate(self.alphabet):
                self.states_dict[i].transitions[letter] = self.states_dict[transition_mapping[i][j]]

    def construct_hypothesis(self, transition_mapping=None, output_mapping=None):
        # Construct a hypothesis (Mealy Machine) based on the observation tree
        self.construct_hypothesis_states(output_mapping=output_mapping)
        self.construct_hypothesis_transitions(transition_mapping=transition_mapping, output_mapping=output_mapping)

        automaton_class = {'dfa': Dfa, 'mealy': MealyMachine, 'moore': MooreMachine}
        hypothesis = automaton_class[self.automaton_type](
            self.states_dict[0], self.states_dict)
        hypothesis.compute_prefixes()
        hypothesis.characterization_set = hypothesis.compute_characterization_set(raise_warning=False)

        return hypothesis

    def passive(self):
        """
        Find a hypothesis consistent with the observation tree, using the pySMT solver.
        There are 2 free functions: "out" and "m" and 1 bound function "delta".
        """
        print("Trying to build hypothesis of size", self.size)
        print(f"Basis size: {len(self.guaranteed_basis)}, Frontier size: {len(self.frontier_to_basis_dict)}")
        start_smt_time = time.time()

        s = Solver(name="z3", solver_options={"timeout": 60000})  # or another backend supported by pySMT

        # Function declarations
        delta = Symbol("delta", FunctionType(INT, [INT, INT]))  # d: int × int → int
        F = Symbol("F", FunctionType(BOOL, [INT]))  # F: int → bool
        D = Symbol("D", FunctionType(INT, [INT]))  # D: int → int

        # Flatten the tree to a list of nodes
        queue = deque([self.root])
        nodes = [self.root]

        # print(list(map(self.get_access_sequence, self.basis)))
        while queue:
            node = queue.popleft()
            # print(self.get_access_sequence(node))
            # print(self._get_output_sequence(['1', '1', '0']))
            idx = nodes.index(node)
            for letter, succ in node.successors.items():
                # Check if successor can reach a known node
                queue2 = deque([succ])
                while queue2:
                    node2 = queue2.popleft()
                    if self.is_known(node2) or node2 in self.guaranteed_basis:
                        break
                    for succ2 in node2.successors.values():
                        queue2.append(succ2)
                else: 
                    continue
                queue.append(succ)
                s.add_assertion(
                    Function(D, [Int(len(nodes))]).Equals(
                    Function(delta, [Function(D, [Int(idx)]), Int(self.alphabet.index(letter))]))
                )
                # if self.get_access_sequence(succ) in [['1', '1', '0'], ['1', '1'], ['1'], []]:
                # print("here")
                # print(constraints[-1])
                nodes.append(succ)
        # print("Nodes in the observation tree:", len(nodes))

        # Basis nodes map to different states
        for i, node in enumerate(self.guaranteed_basis):
            s.add_assertion(Function(D, [Int(nodes.index(node))]).Equals(Int(i)))
        # s.add_assertion(Function(D, [Int(0)]).Equals(Int(0)))  # Root is state 0

        # Force known outputs
        for i, node in enumerate(nodes):
            if self.is_known(node):
                val = Bool(node.output)
                s.add_assertion(Function(F, [Function(D, [Int(i)])]).Iff(val))
                # if(self.get_access_sequence(node) == ['1', '1', '0']):
                # print("here")
                # print(constraints[-1])
            # else:
            #     # Force to true, as a guess
            #     s.add_assertion(Function(F, [Function(D, [Int(i)])]).Iff(Bool(True)))

        for node, candidates in self.frontier_to_basis_dict.items():
            if node not in nodes:
                continue
            s.add_assertion(Or([
                Function(D, [Int(nodes.index(node))]).Equals(Int(self.guaranteed_basis.index(c)))
                for c in candidates
            ] + [Function(D, [Int(nodes.index(node))]).Equals(Int(i)) for i in range(len(self.guaranteed_basis), self.size)]))

        # Correct delta
        for i in range(self.size):
            for j in range(len(self.alphabet)):
                d_ij = Function(delta, [Int(i), Int(j)])
                s.add_assertion(GE(d_ij, Int(0)))
                s.add_assertion(LT(d_ij, Int(self.size)))

        # Fix known delta transitions for basis to basis nodes
        # for i, node in enumerate(self.basis):
        #     for letter, succ in node.successors.items():
        #         if succ in self.basis:
        #             s.add_assertion(
        #                 Function(delta, [Int(i), Int(self.alphabet.index(letter))]) \
        #                     .Equals(Int(self.basis.index(succ)))
        #             )

        try:
            # print("Solving...")
            if not s.solve():
                print("UNSAT")
                print("No hypothesis of size", self.size, "exists")
                self.smt_time += time.time() - start_smt_time
                return None, None
            else:
                # print("SAT")
                self.smt_time += time.time() - start_smt_time
                model = s.get_model()

                transition_mapping = [[None for _ in range(len(self.alphabet))] for _ in range(self.size)]
                output_mapping = [None for _ in range(self.size)]

                for i in range(self.size):
                    val = model.get_value(Function(F, [Int(i)]))
                    output_mapping[i] = str(val) == "True"
                    for j in range(len(self.alphabet)):
                        val = model.get_value(Function(delta, [Int(i), Int(j)]))
                        transition_mapping[i][j] = int(str(val))
                # for node in self.basis:
                #     val = model.get_value(Function(F, [Function(D, [Int(nodes.index(node))])]))
                #     output_mapping[node] = str(val) == "True"

                # for node in self.frontier_to_basis_dict.keys():
                #     val = model.get_value(Function(D, [Int(nodes.index(node))]))
                #     # print(type(val), str(val))
                #     transition_mapping[node] = self.basis[int(str(val))]

                # print(model.get_value(Function(F, [Function(D, [Int(13)])])))
                # print(model.get_value(Function(D, [Int(13)])))
                # print(len(self.basis), len(self.frontier_to_basis_dict), len(nodes))

                return transition_mapping, output_mapping
        except SolverReturnedUnknownResultError:
            self.smt_time += time.time() - start_smt_time
            print("TIMEOUT")
            print("Could not find hypothesis of size", self.size)
            return None, None

    def build_hypothesis(self):
        """
        Builds the hypothesis which will be sent to the SUL and checks consistency
        """
        while True:
            self.find_adequate_observation_tree()
            self.rule4_applications += 1
            # transition_mapping, output_mapping = self.solve_blanks()
            transition_mapping, output_mapping = self.passive()
            if transition_mapping is not None:
                hypothesis = self.construct_hypothesis(transition_mapping=transition_mapping,
                                                       output_mapping=output_mapping)
                return hypothesis
            else:
                self.size += 1
                self.bases_analyzed += 1
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
        while self.promote_frontier_node_in_queue_reset():
            self.update_frontier()
            self.expand_frontier()

        while self.make_frontiers_identified():
            self.update_frontier_to_basis_dict()
            while self.promote_frontier_node_in_queue_reset():
                self.update_frontier()
                self.expand_frontier()

    # Counterexample Processing

    def process_counter_example(self, hypothesis, cex_inputs, cex_outputs):
        """
        Inserts the counter example into the observation tree and searches for the
        input-output sequence which is different
        """
        if type(cex_outputs) not in [list, tuple]:
            # print("Here")
            # self.insert_observation(cex_inputs, cex_outputs)
            cex_outputs, _ = self._get_output_sequence(cex_inputs, query_mode="full")
            # print(cex_inputs)
            # print(cex_outputs)
            self.insert_observation_sequence(cex_inputs, cex_outputs)
            # # Count how many steps the counterexample is away from the guaranteed basis
            # node = self.get_successor(cex_inputs)
            # steps_from_basis = 0
            # while node not in self.guaranteed_basis and node is not None:
            #     node = node.parent
            #     steps_from_basis += 1
            # print(f"Counterexample is {steps_from_basis} steps away from guaranteed basis")
            return
            hyp_outputs = hypothesis.compute_output_seq(
                hypothesis.initial_state, cex_inputs)
            prefix_index = self._get_counter_example_prefix_index(
                cex_outputs, hyp_outputs)
            self._process_linear_search(
                hypothesis, cex_inputs[:prefix_index + 1], cex_outputs[:prefix_index + 1])
        else:
            print("there")
            self.insert_observation_sequence(cex_inputs, cex_outputs)
            hyp_outputs = hypothesis.compute_output_seq(
                hypothesis.initial_state, cex_inputs)
            prefix_index = self._get_counter_example_prefix_index(
                cex_outputs, hyp_outputs)
            self._process_linear_search(
                hypothesis, cex_inputs[:prefix_index + 1], cex_outputs[:prefix_index + 1])

    def _get_counter_example_prefix_index(self, cex_outputs, hyp_outputs):
        """
        Checks at which index the output functions differ 
        """
        for index in range(len(cex_outputs)):
            if cex_outputs[index] != hyp_outputs[index] and not (
                    cex_outputs[index] is None or
                    cex_outputs[index] == "unknown" or
                    hyp_outputs[index] is None or
                    hyp_outputs[index] == "unknown"
            ):
                return index
        raise RuntimeError("counterexample and hypothesis outputs are equal")

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
                    # self.queries += 1
                    # print(self.queries)
                    queried = True
                else:
                    outputs.append(None)
            else:
                if current_node.output is None and (
                        query_mode == "full" or (inp_num == len(inputs) - 1 and query_mode == "final")):
                    outputs.append(self.sul.query(inputs[:inp_num + 1]))
                    # self.queries += 1
                    # print(self.queries)
                    queried = True
                else:
                    outputs.append(current_node.output)
        return outputs, queried

    def _process_binary_search(self, hypothesis, cex_inputs, cex_outputs):
        """
        use binary search on the counter example to compute a witness between the real system and the hypothesis
        """
        tree_node = self.get_successor(cex_inputs)

        if tree_node in self.frontier_to_basis_dict or tree_node in self.basis:
            return None

        hyp_state = self._get_automaton_successor(
            hypothesis, hypothesis.initial_state, cex_inputs)
        hyp_node = list(self.states_dict.keys())[list(
            self.states_dict.values()).index(hyp_state)]

        prefix = []
        current_state = self.root
        for input in cex_inputs:
            if current_state in self.frontier_to_basis_dict:
                break
            current_state = current_state.get_successor(input)
            prefix.append(input)

        h = (len(prefix) + len(cex_inputs)) // 2
        sigma1 = list(cex_inputs[:h])
        sigma2 = list(cex_inputs[h:])

        hyp_state_p = self._get_automaton_successor(
            hypothesis, hypothesis.initial_state, sigma1)
        hyp_node_p = list(self.states_dict.keys())[list(
            self.states_dict.values()).index(hyp_state_p)]
        hyp_p_access = self.get_transfer_sequence(self.root, hyp_node_p)

        witness = Apartness.compute_witness(tree_node, hyp_node, self)
        if witness is None:
            return None

        query_inputs = hyp_p_access + sigma2 + witness
        query_outputs, _ = self._get_output_sequence(query_inputs, query_mode="final")

        self.insert_observation_sequence(query_inputs, query_outputs)

        tree_node_p = self.get_successor(sigma1)

        witness_p = Apartness.compute_witness(tree_node_p, hyp_node_p, self)

        if witness_p is not None:
            self._process_binary_search(hypothesis, sigma1, cex_outputs[:h])
        else:
            new_inputs = list(hyp_p_access) + sigma2
            self._process_linear_search(
                hypothesis, new_inputs, query_outputs[:len(new_inputs)])

        return None

    def _process_linear_search(self, hypothesis, cex_inputs, cex_outputs):
        """
        use binary search on the counter example to compute a witness between the real system and the hypothesis
        """
        nodes_dict = {}
        for hyp_node, hyp_state in self.states_dict.items():
            nodes_dict[hyp_state] = hyp_node

        access_seq = cex_inputs
        tree_node = self.get_successor(cex_inputs)
        witness_seq = []
        while not (tree_node in self.frontier_to_basis_dict or
                   tree_node in self.basis):
            witness_seq = [access_seq[-1]] + witness_seq
            access_seq = access_seq[:-1]

            tree_node = tree_node.parent
            hyp_state = self._get_automaton_successor(
                hypothesis,
                hypothesis.initial_state,
                access_seq
            )
            hyp_node = nodes_dict[hyp_state]
            hyp_access = self.get_transfer_sequence(self.root, hyp_node)

            hyp_output = self._get_automaton_successor(
                hypothesis,
                hyp_state,
                witness_seq
            ).output

            witness_node = self.get_successor(witness_seq, start_node=hyp_node)
            if witness_node is None or witness_node.output is None:
                output_seq, _ = self._get_output_sequence(
                    hyp_access + witness_seq,
                    query_mode='final'
                )
                self.insert_observation_sequence(
                    hyp_access + witness_seq,
                    output_seq
                )
                # print(hyp_access, witness_seq,  "inserted")
                witness_node = self.get_successor(witness_seq, start_node=hyp_node)
            else:
                # print(hyp_access, witness_seq, "not new")
                '''
                No new information will be inserted, since node is already explored.
                Either the node is consistent with hypothesis, 
                or it has been inserted during the counter example processing.
                To prevent looping we ignore it.
                '''
                continue

            tree_output = witness_node.output

            if Apartness.incompatible_output(hyp_output, tree_output):
                access_seq = hyp_access + witness_seq
                tree_node = self.get_successor(access_seq)
                witness_seq = []
                # print(hyp_output, "!=", tree_output)
        # print("process_linear_search done")

    def _get_automaton_successor(self, automaton, from_state, inputs):
        """
        get the automaton successor of a state
        """
        automaton.current_state = from_state
        for inp in inputs:
            automaton.current_state = automaton.current_state.transitions[inp]

        return automaton.current_state
