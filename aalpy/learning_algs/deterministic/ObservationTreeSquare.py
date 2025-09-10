import time
from collections import deque
import copy
from math import log, ceil

# from .ADS import Ads
from .Apartness import Apartness
from ... import Dfa, DfaState, MealyState, MealyMachine, MooreMachine, MooreState
import z3
from .ObservationTree import MooreNode, MealyNode

# Supported automata types
aut_type = ['dfa']


class ObservationTreeSquare:
    def __init__(self, alphabet, sul, automaton_type):
        """
        Initializes the observation tree with a root node.
        :param alphabet: Input alphabet
        :param sul: System under learning
        :param automaton_type: Type of automaton to learn
        """
        assert automaton_type in aut_type
        assert alphabet is not None and sul is not None

        # Logger information
        self.smt_time = 0
        self.rule1_applications = 0
        self.rule2_applications = 0
        self.rule3_applications = 0
        self.rule4_applications = 0
        self.bases_analyzed = 1
        MooreNode._id_counter = 0
        MealyNode._id_counter = 0

        # Initialize tree
        self.alphabet = alphabet
        self.sul = sul
        self.automaton_type = automaton_type
        self.outputAlphabet = [True, False, "unknown"]

        self.root = MooreNode()
        self.root.output = self.sul.query([])

        self.basis = [self.root]
        self.guaranteed_basis = [self.root]
        self.queue = deque()
        self.frontier_to_basis_dict = dict()

    def insert_observation(self, inputs, output_val):
        """
        Insert an observation into the tree using sequences of inputs and the corresponding output.
        :param inputs: List of inputs
        :param output_val: Output corresponding to the input sequence
        """
        current_node = self.root
        for input_val in inputs:
            current_node = current_node.extend_and_get(input_val, None)
        current_node.output = output_val

    def insert_observation_sequence(self, inputs, outputs):
        """
        Insert an observation into the tree using sequences of inputs and their corresponding outputs.
        :param inputs: List of inputs
        :param outputs: Outputs corresponding to the input sequence
        """
        if len(inputs) != len(outputs):
            raise ValueError("Inputs and outputs must have the same length.")

        current_node = self.root
        for input_val, output_val in zip(inputs, outputs):
            current_node = current_node.extend_and_get(input_val, output_val)
            current_node.output = output_val

    def get_observation(self, inputs):
        """
        Retrieve the list of outputs based on a given input sequence
        """
        current_node = self.root
        observation = []
        for input_val in inputs:
            current_node = current_node.get_successor(input_val)
            output = current_node.output
            if output is None:
                return None
            observation.append(output)
        return observation

    def get_outputs(self, basis_node, inputs):
        """
        Retrieve the list of outputs based on a basis node and a given input sequence
        """
        prefix = self.get_transfer_sequence(self.root, basis_node)
        current_node = self.get_successor(prefix)
        observation = []
        for input_val in inputs:
            output = current_node.output
            if output is None:
                return None
            observation.append(output)
            current_node = current_node.get_successor(input_val)
        return observation

    def get_successor(self, inputs, from_node=None):
        """
        Retrieve the node (subtree) corresponding to the given input sequence
        """
        if from_node is None:
            current_node = self.root
        else:
            current_node = from_node
        for input_val in inputs:
            successor_node = current_node.get_successor(input_val)
            if successor_node is None:
                return None
            current_node = successor_node
        return current_node

    @staticmethod
    def get_transfer_sequence(from_node, to_node):
        """
        Get the transfer sequence (inputs) that moves from one node to another
        """
        transfer_sequence = []
        current_node = to_node

        while current_node != from_node:
            if current_node.parent is None:
                return None
            transfer_sequence.append(current_node.input_to_parent)
            current_node = current_node.parent

        transfer_sequence.reverse()
        return transfer_sequence

    def get_access_sequence(self, to_node):
        """
        Get the transfer sequence (inputs) that moves from one node to another
        """
        transfer_sequence = []
        current_node = to_node

        while current_node != self.root:
            if current_node.parent is None:
                return None
            transfer_sequence.append(current_node.input_to_parent)
            current_node = current_node.parent

        transfer_sequence.reverse()
        return transfer_sequence

    def get_size(self):
        return self.root.id_counter

    @staticmethod
    def is_known(node):
        return node.output is not None and node.output != "unknown"

    def count_informative_nodes(self):
        """
        counts how many nodes have informative information
        """
        node_queue = deque()
        node_queue.append(self.root)
        count = 0
        while node_queue:
            node = node_queue.popleft()
            if self.is_known(node):
                count += 1
            for successor in node.successors.values():
                node_queue.append(successor)
        return count

    # Functions related to finding new basis and frontier nodes
    def update_frontier_and_basis(self):
        """
        Updates the frontier to basis map, promotes a frontier node and checks for consistency
        """
        self.update_frontier_to_basis_dict()
        self.promote_frontier_node_in_queue_reset()
        self.check_frontier_consistency()
        self.update_frontier_to_basis_dict()

    def update_basis_candidates(self, frontier_node):
        """
        Updates the basis candidates for the specified frontier node.
        Removes basis nodes that are deemed apart from the frontier node.
        """
        if frontier_node not in self.frontier_to_basis_dict:
            print(
                f"Warning: {frontier_node} not found in frontier_to_basis_dict.")
            return

        basis_list = self.frontier_to_basis_dict[frontier_node]
        new_basis_list = [basis_node for basis_node in basis_list if
                          not Apartness.states_are_apart(frontier_node, basis_node, self)]
        self.frontier_to_basis_dict[frontier_node] = new_basis_list

    def update_frontier_to_basis_dict(self):
        """
        Checks for basis candidates (basis nodes with the same behavior) for each frontier node.
        If a frontier node and a basis node are "apart", the basis node is removed from the basis list.
        """
        for frontier_node, basis_list in self.frontier_to_basis_dict.items():
            new_basis_list = [basis_node for basis_node in basis_list if
                              not Apartness.states_are_apart(frontier_node, basis_node, self)]
            self.frontier_to_basis_dict[frontier_node] = new_basis_list

    def add_frontier_to_queue(self, new_basis_node):
        """
        adds a new basis to the queue with all nodes in the current basis + the new basis node
        """
        new_basis = self.basis.copy()
        new_frontier_to_basis_dict = {k: self.frontier_to_basis_dict[k].copy() for k in self.frontier_to_basis_dict}

        new_basis.append(new_basis_node)
        del new_frontier_to_basis_dict[new_basis_node]

        for frontier_node, new_basis_options in new_frontier_to_basis_dict.items():
            if not Apartness.states_are_apart(new_basis_node, frontier_node, self):
                new_basis_options.append(new_basis_node)
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
                    if not Apartness.states_are_apart(new_basis, frontier_node, self):
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
                # New basis: guaranteed basis + isolated node (preserving order)
                new_basis = self.guaranteed_basis.copy()
                new_basis.append(iso_frontier_node)
                # Remove the isolated node from the frontier
                new_frontier_to_basis_dict = {k: v.copy() for k, v in self.frontier_to_basis_dict.items() if
                                              k != iso_frontier_node}
                # Update basis candidates for remaining frontier nodes
                for frontier_node, new_basis_list in new_frontier_to_basis_dict.items():
                    new_basis_list[:] = [b for b in new_basis if
                                         not Apartness.states_are_apart(b, frontier_node, self)]
                # Reset the queue to only contain the new minimal basis
                self.queue.clear()
                self.queue.append((new_basis, new_frontier_to_basis_dict))
                self.basis, self.frontier_to_basis_dict = self.queue.popleft()
                # Update guaranteed_basis as well
                self.guaranteed_basis = new_basis.copy()
                self.bases_analyzed += 1
                self.rule1_applications += 1
                break

    def promote_frontier_node_in_queue_filter(self):
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
                    if not Apartness.states_are_apart(new_basis, frontier_node, self):
                        new_basis_list.append(new_basis)
                already_in_queue = False
                for basis2, _ in self.queue:
                    if set(basis2) == set(self.basis):
                        already_in_queue = True
                if not already_in_queue:
                    self.queue.append((self.basis, self.frontier_to_basis_dict))
                filtered_queue = []
                for basis2, f2b2 in self.queue:
                    if iso_frontier_node in basis2:
                        filtered_queue.append((basis2, f2b2))
                # print("Filtered queue base lengths:", [len(basis2) for basis2, _ in filtered_queue])
                self.queue = deque(filtered_queue)
                self.basis, self.frontier_to_basis_dict = self.queue.popleft()
                self.bases_analyzed += 1
                self.rule1_applications += 1
                break

    def check_frontier_consistency(self):
        """
        Checks if all the states are correctly defined and creates new frontier nodes when possible 
        """
        for basis_node in self.basis:
            for i in self.alphabet:
                maybe_frontier = basis_node.get_successor(i)

                if maybe_frontier is None:
                    self.explore_frontier(basis_node, i)
                    self.rule2_applications += 1
                    maybe_frontier = basis_node.get_successor(i)

                if (self.automaton_type == 'moore' or self.automaton_type == 'dfa') and maybe_frontier.output is None:
                    inputs = self.get_transfer_sequence(self.root, maybe_frontier)
                    outputs = self._get_output_sequence(inputs, query_mode="full")
                    self.insert_observation_sequence(inputs, outputs)
                    assert maybe_frontier.output is not None

                if maybe_frontier in self.basis or maybe_frontier in self.frontier_to_basis_dict:
                    continue

                self.frontier_to_basis_dict[maybe_frontier] = [
                    new_basis_node for new_basis_node in self.basis
                    if not Apartness.states_are_apart(new_basis_node, maybe_frontier, self)
                ]

    def is_observation_tree_adequate(self):
        """
        Check for each frontier node if they have only 1 basis candidate, 
        or have multiple candidates but no more witnesses to narrow it down. 
        Also check if all basis nodes have some output for every input.
        """
        self.check_frontier_consistency()
        for frontier_node, basis_list in self.frontier_to_basis_dict.items():
            if frontier_node.output is None:
                return False
            if len(basis_list) != 1:
                if len(basis_list) > 1:
                    if self.automaton_type == 'mealy':
                        distinguishing_sequences = Apartness._get_distinguishing_sequences_mealy(basis_list,
                                                                                                 self.alphabet)
                        for distinguishing_sequence in distinguishing_sequences:
                            inputs = list(self.get_access_sequence(frontier_node))
                            inputs = inputs + distinguishing_sequence[:len(distinguishing_sequence) - 1]
                            lastInput = distinguishing_sequence[len(distinguishing_sequence) - 1]
                            distinguishingNode = self.get_successor(inputs)
                            if distinguishingNode is not None and (distinguishingNode.get_output(
                                    lastInput) != "unknown" and distinguishingNode.get_output(lastInput) is not None):
                                return False
                    else:
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
            if not Apartness.states_are_apart(new_basis_node, new_frontier, self)
        }

    def explore_frontier(self, basis_node, inp):
        """
        Explores a specific frontier node (basis node + input) by passing a query to the SUL
        """
        inputs = self.get_transfer_sequence(self.root, basis_node) + [inp]
        outputs = self._get_output_sequence(inputs)
        self.insert_observation_sequence(inputs, outputs)

    def make_frontiers_identified(self):
        """
        Loop over all frontier nodes to identify them
        """
        for frontier_node in self.frontier_to_basis_dict:
            self.identify_frontier(frontier_node)

    def identify_frontier(self, frontier_node):
        """
        Identify a specific frontier node
        """
        if frontier_node not in self.frontier_to_basis_dict:
            raise Exception(
                f"Warning: {frontier_node} not found in frontier_to_basis_dict.")

        self.update_basis_candidates(frontier_node)
        old_candidate_size = len(
            self.frontier_to_basis_dict.get(frontier_node))
        if old_candidate_size < 2:
            return

        inputs_to_frontier = self.get_transfer_sequence(self.root, frontier_node)

        witnesses = self._get_witnesses_bfs(frontier_node)
        for witness_seq in witnesses:
            self.rule3_applications += 1

            inputs = inputs_to_frontier + witness_seq
            outputs = self._get_output_sequence(inputs, query_mode='final')
            self.insert_observation_sequence(inputs, outputs)
            if outputs[-1] != "unknown":
                break

        self.update_basis_candidates(frontier_node)

    def _get_witnesses_bfs(self, frontier_node):
        """
        Specifically identify frontier nodes using separating sequences
        """
        basis_candidates = self.frontier_to_basis_dict.get(frontier_node)
        witnesses = Apartness._get_distinguishing_sequences(basis_candidates, self)

        for witness_seq in witnesses:
            leads_to_node = self.get_successor(witness_seq, from_node=frontier_node)
            if leads_to_node is None or leads_to_node.output is None:
                yield witness_seq

    def construct_hypothesis_states(self, output_mapping=None):
        """
        Construct the hypothesis states from the basis
        """
        self.states_dict = dict()
        state_counter = 0

        for basis_node in self.basis:
            state_id = f's{state_counter}'
            if self.automaton_type == 'dfa':
                self.states_dict[basis_node] = DfaState(state_id)
                if basis_node.output == "unknown":
                    self.states_dict[basis_node].is_accepting = output_mapping[basis_node]
                else:
                    self.states_dict[basis_node].is_accepting = basis_node.output
            elif self.automaton_type == 'moore':
                if basis_node.output == "unknown":
                    self.states_dict[basis_node] = MooreState(
                        state_id, output=output_mapping[basis_node])
                else:
                    self.states_dict[basis_node] = MooreState(
                        state_id, output=basis_node.output)
            else:
                self.states_dict[basis_node] = MealyState(state_id)
            state_counter += 1

    def construct_hypothesis_transitions(self, transition_mapping=None, output_mapping=None):
        """
        Construct the hypothesis transitions using the transition_mapping and output_mapping.
        """
        for basis_node in self.basis:
            for input_val in self.alphabet:
                # set transition
                successor = basis_node.get_successor(input_val)
                if successor in self.frontier_to_basis_dict:
                    # set successor for frontier node
                    candidates = self.frontier_to_basis_dict[successor]
                    if transition_mapping is None:
                        successor = next(iter(candidates))
                    else:
                        successor = transition_mapping[successor]
                if successor not in self.states_dict:
                    raise RuntimeError(
                        "Successor is not in the basisToStateMap.")

                destination = self.states_dict[successor]
                self.states_dict[basis_node].transitions[input_val] = destination
                if self.automaton_type == 'mealy':
                    if basis_node.get_output(input_val) == "unknown":
                        self.states_dict[basis_node].output_fun[input_val] = output_mapping[(basis_node, input_val)]
                    else:
                        self.states_dict[basis_node].output_fun[input_val] = basis_node.get_output(input_val)

    def construct_hypothesis(self, transition_mapping=None, output_mapping=None):
        # Construct a hypothesis (Mealy Machine) based on the observation tree
        self.construct_hypothesis_states(output_mapping=output_mapping)
        self.construct_hypothesis_transitions(transition_mapping=transition_mapping, output_mapping=output_mapping)

        automaton_class = {'dfa': Dfa, 'mealy': MealyMachine, 'moore': MooreMachine}
        hypothesis = automaton_class[self.automaton_type](
            self.states_dict[self.root], list(self.states_dict.values()))
        hypothesis.compute_prefixes()
        hypothesis.characterization_set = hypothesis.compute_characterization_set(raise_warning=False)

        return hypothesis

    def fill_blanks(self):
        assert self.automaton_type == "moore" or self.automaton_type == "dfa", "mealy not implemented yet"
        transition_mapping = dict()
        output_mapping = dict()

        basis = self.basis
        basis_len = len(basis)
        basis_bits = ceil(log(basis_len, 2)) if basis_len > 1 else 1
        frontier = list(self.frontier_to_basis_dict.keys())
        frontier_len = len(frontier)
        frontier_bits = ceil(log(basis_len + frontier_len, 2)) if (basis_len + frontier_len) > 1 else 1
        input_alphabet = self.alphabet
        input_alphabet_len = len(input_alphabet)
        input_alphabet_bits = ceil(log(input_alphabet_len, 2)) if (input_alphabet_len > 1) else 1

        # each basis has an output
        start_smt_time = time.time()
        s = z3.Solver()

        """
        "m" represents the mapping from frontier/basis nodes to automaton states
        "delta" is the transition function
        "out is the output function
        """
        out = z3.Function('out', z3.IntSort(), z3.BoolSort())
        delta = z3.Function('d', z3.IntSort(), z3.IntSort(), z3.IntSort())
        m = z3.Function('m', z3.IntSort(), z3.IntSort())

        # Flatten the tree to a list of nodes
        queue = deque([self.root])
        nodes = [self.root]
        while queue:
            node = queue.popleft()
            idx = len(nodes) - 1
            for i in range(input_alphabet_len):
                letter = input_alphabet[i]
                succ = node.get_successor(letter)
                if succ is not None:
                    queue.append(succ)
                    nodes.append(succ)
                    s.add(delta(idx, i) == len(nodes))
                else:
                    s.add(delta(idx, i) == -1)
        nodes_len = len(nodes)

        # Force known outputs
        s.add([out(n) == nodes[n].output for n in range(nodes_len) if self.is_known(nodes[n])])

        # The frontier nodes map to one of its candidates
        for f in range(frontier_len):
            basis_options = [basis.index(b) for b in self.frontier_to_basis_dict[frontier[f]]]
            print(basis_options)
            s.add(z3.Or([m(f) == b for b in basis_options]))

        # The frontier node is not apart from the node it maps to
        for f in range(frontier_len):
            frontier_node = nodes.index(frontier[f])
            basis_node = m(f)
            queue = deque([(frontier_node, basis_node)])
            while queue:
                first, second = queue.popleft()
                s.add(z3.Or(out(first) == out(second), second == -1))
                for letter in input_alphabet:
                    first_succ = nodes[first].get_successor(letter)
                    second_succ = delta(second, input_alphabet.index(letter))
                    if first_succ is not None:
                        queue.append((nodes.index(first_succ), second_succ))

        if s.check() == z3.unsat:
            self.smt_time += time.time() - start_smt_time
            print("unsat")
            return None, None
        else:
            print("sat")
            self.smt_time += time.time() - start_smt_time
            model = s.model()
            for b in range(len(basis)):
                output_mapping[basis[b]] = z3.is_true(model.evaluate(out(b)))
            for f in range(len(frontier)):
                transition_mapping[frontier[f]] = nodes[model.evaluate(m(f)).as_long()]

            return transition_mapping, output_mapping

    def find_mapping(self):
        """
        Find a hypothesis consistent with the observation tree, using the z3 SMT solver.
        There are 2 free functions: "out" and "m" and 1 bound function "delta".
        """
        assert self.automaton_type == "moore" or self.automaton_type == "dfa", "mealy not implemented yet"
        transition_mapping = dict()
        output_mapping = dict()

        basis = self.basis
        frontier = list(self.frontier_to_basis_dict.keys())
        input_alphabet = self.alphabet
        output_alphabet = self.outputAlphabet.copy()
        if "unknown" in output_alphabet:
            output_alphabet.remove("unknown")
        if None in output_alphabet:
            output_alphabet.remove(None)
        if not output_alphabet:
            output_alphabet = [False, True]

        # each basis has an output
        start_smt_time = time.time()
        s = z3.Solver()
        # s.set(unsat_core=True)
        """
        "m" represents the mapping from frontier/basis nodes to automaton states
        "delta" is the transition function
        "out is the output function
        """
        out = z3.Function('out', z3.IntSort(), z3.BoolSort())
        delta = z3.Function('d', z3.IntSort(), z3.IntSort(), z3.IntSort())
        m = z3.Function('m', z3.IntSort(), z3.IntSort())
        # basis nodements
        for b in range(len(basis)):
            # out function
            # if output value basis i known then out(i) must be corresponding index
            # else make sure output value is index in OutputAlphabet
            if basis[b].output != "unknown":
                s.add(out(b) == basis[b].output)
            # d transitions
            for input_index in range(len(input_alphabet)):
                to_node = basis[b].get_successor(input_alphabet[input_index])
                if to_node in basis:
                    s.add(delta(b, input_index) == basis.index(to_node))
                else:
                    s.add(delta(b, input_index) == len(basis) + frontier.index(to_node))
            # m mapping
            s.add(m(b) == b)

        queue = []  # (node, equation to base (number))
        # frontier nodements and making queue
        for f in range(len(frontier)):
            # m mapping
            basis_options = [basis.index(b) for b in self.frontier_to_basis_dict[frontier[f]]]
            s.assert_and_track(z3.Or([m(f + len(basis)) == b for b in basis_options]), f'{f}')
            s.add(z3.Or([m(f + len(basis)) == b for b in basis_options]))
            # out function
            if frontier[f].output != "unknown":
                s.add(out(m(f + len(basis))) == frontier[f].output)
            # add to queue
            for input_index in range(len(input_alphabet)):
                node = frontier[f].get_successor(input_alphabet[input_index])
                if not node is None:
                    eq_to_base_num = m(delta(m(f + len(basis)), input_index))
                    queue.append((node, eq_to_base_num))
        while queue:
            node, eq_to_base_num = queue.pop(0)
            if node.output != "unknown" and node.output is not None:
                s.add(out(eq_to_base_num) == node.output)
            # add more to queue
            for input_index in range(len(input_alphabet)):
                node2 = node.get_successor(input_alphabet[input_index])
                if not node2 is None:
                    eq_to_base_num2 = m(delta(eq_to_base_num, input_index))
                    queue.append((node2, eq_to_base_num2))

        if s.check() == z3.unsat:
            self.smt_time += time.time() - start_smt_time
            # unsat_core = set(map(lambda x: frontier[int(x.decl().name())], s.unsat_core()))
            # print(unsat_core)
            # return None, unsat_core
            return None, None
        else:
            self.smt_time += time.time() - start_smt_time
            model = s.model()
            for b in range(len(basis)):
                output_mapping[basis[b]] = z3.is_true(model.evaluate(out(b)))
            for f in range(len(frontier)):
                transition_mapping[frontier[f]] = basis[model.evaluate(m(f + len(basis))).as_long()]

            return transition_mapping, output_mapping

    def passive(self):
        """
        Find a hypothesis consistent with the observation tree, using the z3 SMT solver.
        There are 2 free functions: "out" and "m" and 1 bound function "delta".
        """
        assert self.automaton_type == "moore" or self.automaton_type == "dfa", "mealy not implemented yet"

        start_smt_time = time.time()
        s = z3.Solver()

        delta = z3.Function('d', z3.IntSort(), z3.IntSort(), z3.IntSort())
        F = z3.Function('F', z3.IntSort(), z3.BoolSort())
        D = z3.Function('D', z3.IntSort(), z3.IntSort())

        # Flatten the tree to a list of nodes
        queue = deque([self.root])
        nodes = [self.root]
        while queue:
            node = queue.popleft()
            idx = nodes.index(node)
            for letter, succ in node.successors.items():
                queue.append(succ)
                s.add(D(len(nodes)) == delta(D(idx), self.alphabet.index(letter)))
                nodes.append(succ)

        """
        "m" represents the mapping from frontier/basis nodes to automaton states
        "delta" is the transition function
        "out is the output function
        """


        # Basis nodes map to themselves
        for i in range(len(self.basis)):
            node = self.basis[i]
            s.add(D(nodes.index(node)) == i)

        # Force known outputs
        for i in range(len(nodes)):
            if self.is_known(nodes[i]):
                s.add(F(D(i)) == nodes[i].output)

        # Frontiers only map to candidates
        for node, candidates in self.frontier_to_basis_dict.items():
            s.add(z3.Or([D(nodes.index(node)) == self.basis.index(c) for c in candidates]))

        # Correct delta
        for i in range(len(self.basis)):
            for j in range(len(self.alphabet)):
                s.add(0 <= delta(i, j))
                s.add(delta(i, j) < len(self.basis))

        # Fix known delta transitions for basis to basis nodes
        # for i in range(len(self.basis)):
        #     node = self.basis[i]
        #     for letter, succ in node.successors.items():
        #         if succ in self.basis:
        #             s.add(delta(i, self.alphabet.index(letter)) == self.basis.index(succ))

        transition_mapping = dict()
        output_mapping = dict()

        if s.check() == z3.unsat:
            self.smt_time += time.time() - start_smt_time
            # unsat_core = set(map(lambda x: frontier[int(x.decl().name())], s.unsat_core()))
            # print(unsat_core)
            # return None, unsat_core
            return None, None
        else:
            self.smt_time += time.time() - start_smt_time
            model = s.model()
            for node in self.basis:
                output_mapping[node] = z3.is_true(model.evaluate(F(D(nodes.index(node)))))
            for node in self.frontier_to_basis_dict.keys():
                transition_mapping[node] = self.basis[model.evaluate(D(nodes.index(node))).as_long()]

            return transition_mapping, output_mapping

    def solve_blanks(self):
        assert self.automaton_type == "dfa"
        basis = self.basis
        frontier = list(self.frontier_to_basis_dict.keys())
        input_alphabet = self.alphabet
        output_alphabet = [True, False]

        s = z3.Solver()
        s.set(unsat_core=True)
        start_smt_time = time.time()

        # Create a variable for each node in the observation tree.
        # These variables represent the output (True/False) of each node.
        # We use BFS to traverse the tree and create variables.
        # We immediately add constraints to set the correct range for each variable,
        # namely that it must correspond to what we already know about the output.
        queue = deque([self.root])
        out = dict()
        while queue:
            node = queue.popleft()
            node_var = z3.Bool(f'out_{node.id}')
            out[node] = node_var
            if self.is_known(node):
                s.add(node_var == node.output)
            for successor in node.successors.values():
                queue.append(successor)

        frontier = list(self.frontier_to_basis_dict.keys())

        # Add constraints to ensure that each frontier node is
        # not apart from at least one basis node.
        for frontier_node, basis_list in self.frontier_to_basis_dict.items():
            # We can assume that basis_list is not empty,
            # otherwise we would have promoted this frontier node.

            # Keep track of the constraints for non-apartness for each basis node
            not_apart_constraints = []
            visited = set()
            for basis_node in basis_list:
                # Keep track of the constraints for non-apartness for this specific basis node
                not_apart_constraint = []
                # BFS over pairs of nodes starting from (frontier_node, basis_node)
                pairs = deque([(frontier_node, basis_node)])
                while pairs:
                    first_node, second_node = pairs.popleft()
                    if (first_node, second_node) in visited:
                        continue
                    visited.add((first_node, second_node))
                    # The outputs must be the same for non-apartness
                    constraint = (out[first_node] == out[second_node])
                    not_apart_constraint.append(constraint)
                    for input_val in input_alphabet:
                        # Add the successors to the queue, if they both exist
                        first_succ = first_node.get_successor(input_val)
                        second_succ = second_node.get_successor(input_val)
                        if first_succ is not None and second_succ is not None:
                            pairs.append((first_succ, second_succ))
                # Combine all constraints for this basis node with AND
                if not_apart_constraint:
                    not_apart_constraints.append(z3.And(not_apart_constraint))
            # Combine the non-apartness constraints for all basis nodes with OR
            if not_apart_constraints:
                # print(f"Adding {len(not_apart_constraints)} not apart constraints")
                s.assert_and_track(z3.Or(not_apart_constraints), f'{frontier.index(frontier_node)}')
                s.add(z3.Or(not_apart_constraints))
        # print(" ")

        if s.check() == z3.unsat:
            self.smt_time += time.time() - start_smt_time
            unsat_core = set(map(lambda x: frontier[int(x.decl().name())], s.unsat_core()))
            return None, unsat_core

        self.smt_time += time.time() - start_smt_time
        model = s.model()

        # Deep copy the observation tree
        self.saved_tree = copy.deepcopy(self.root)
        self.saved_frontier_to_basis_dict = {k: v.copy() for k, v in self.frontier_to_basis_dict.items()}

        # Traverse the copied tree and fill in outputs
        queue = deque([self.root])
        while queue:
            node = queue.popleft()
            if node.output == "unknown":
                # Get the z3 variable name for this node
                node_var = z3.Bool(f'out_{node.id}')
                # Assign the value from the model
                node.output = z3.is_true(model.evaluate(node_var, model_completion=True))
            for successor in node.successors.values():
                queue.append(successor)

        # Update the frontier_to_basis_dict to reflect the new outputs
        self.update_frontier_to_basis_dict()

        # Create the output mapping for the basis nodes
        output_mapping = dict()
        for basis_node in self.basis:
            output_mapping[basis_node] = basis_node.output

        # Create the transition mapping from frontier nodes to basis nodes
        transition_mapping = dict()
        for frontier_node in self.frontier_to_basis_dict:
            candidates = self.frontier_to_basis_dict[frontier_node]
            if candidates:
                transition_mapping[frontier_node] = candidates[0]
            else:
                raise RuntimeError("No basis candidates found for a frontier node after solving blanks.")

        # print(output_mapping)
        # print(transition_mapping)
        # Restore the original tree outputs by traversing both trees simultaneously
        queue = deque([(self.root, self.saved_tree)])
        while queue:
            curr_node, saved_node = queue.popleft()
            curr_node.output = saved_node.output
            for inp in curr_node.successors:
                if inp in saved_node.successors:
                    queue.append((curr_node.successors[inp], saved_node.successors[inp]))

        self.frontier_to_basis_dict = self.saved_frontier_to_basis_dict

        return transition_mapping, output_mapping

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
                counter_example = Apartness.compute_witness_in_tree_and_hypothesis_states(self, self.root,
                                                                                          hypothesis.initial_state)
                if not counter_example:
                    return hypothesis
                # else:
                #     print("Counter example found:", counter_example)

                cex_output = self.get_observation(counter_example)
                self.process_counter_example(hypothesis, counter_example, cex_output)
            else:
                # unsat_core = output_mapping
                addable_frontier_nodes = set(self.frontier_to_basis_dict.keys()).copy()
                # if unsat_core:
                #     addable_frontier_nodes = addable_frontier_nodes.intersection(unsat_core)
                # if addable_frontier_nodes.intersection(set(self.basis)):
                #     print("overlap")
                # addable_frontier_nodes = addable_frontier_nodes - set(self.basis)
                # print(addable_frontier_nodes)
                for basis2, _ in self.queue:
                    if not set(self.basis) - set(basis2):
                        extra_nodes = set(basis2) - set(self.basis)
                        if len(extra_nodes) == 1:
                            node = extra_nodes.pop()
                            if node in addable_frontier_nodes:
                                addable_frontier_nodes.remove(node)
                for frontier_node in addable_frontier_nodes:
                    self.add_frontier_to_queue(frontier_node)
                self.basis, self.frontier_to_basis_dict = self.queue.popleft()
                self.bases_analyzed += 1

    def find_adequate_observation_tree(self):
        """
        Tries to find an observation tree, 
        for which each frontier state is identified as much as possible.
        """
        self.update_frontier_and_basis()
        while not self.is_observation_tree_adequate():
            self.make_frontier_complete()
            self.make_frontiers_identified()
            self.promote_frontier_node_in_queue_reset()

    # Counterexample Processing

    def process_counter_example(self, hypothesis, cex_inputs, cex_outputs):
        """
        Inserts the counter example into the observation tree and searches for the
        input-output sequence which is different
        """
        if type(cex_outputs) not in [list, tuple]:
            cex_outputs = self._get_output_sequence(cex_inputs, query_mode="final")
            self.insert_observation_sequence(cex_inputs, cex_outputs)
            hyp_outputs = hypothesis.compute_output_seq(
                hypothesis.initial_state, cex_inputs)
            prefix_index = self._get_counter_example_prefix_index(
                cex_outputs, hyp_outputs)
            self._process_linear_search(
                hypothesis, cex_inputs[:prefix_index + 1], cex_outputs[:prefix_index + 1])
        else:
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
        if self.automaton_type != "dfa":
            return self.sul.query(inputs)
        else:
            outputs = []
            current_node = self.root
            for inp_num in range(len(inputs)):
                inp = inputs[inp_num]
                if current_node is not None:
                    current_node = current_node.get_successor(inp)
                if current_node is None:
                    if query_mode == "full" or (inp_num == len(inputs) - 1 and query_mode == "final"):
                        outputs.append(self.sul.query(inputs[:inp_num + 1]))
                    else:
                        outputs.append(None)
                else:
                    if current_node.output is None and (
                            query_mode == "full" or (inp_num == len(inputs) - 1 and query_mode == "final")):
                        outputs.append(self.sul.query(inputs[:inp_num + 1]))
                    else:
                        outputs.append(current_node.output)
            return outputs

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
        query_outputs = self._get_output_sequence(query_inputs, query_mode="final")

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

            witness_node = self.get_successor(witness_seq, from_node=hyp_node)
            if witness_node is None or witness_node.output is None:
                output_seq = self._get_output_sequence(
                    hyp_access + witness_seq,
                    query_mode='final'
                )
                self.insert_observation_sequence(
                    hyp_access + witness_seq,
                    output_seq
                )
                # print(hyp_access, witness_seq,  "inserted")
                witness_node = self.get_successor(witness_seq, from_node=hyp_node)
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
