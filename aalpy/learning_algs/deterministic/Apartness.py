from collections import deque
from copy import deepcopy
from copy import copy

class MooreNode:
    _id_counter = 0
    __slots__ = ['id', 'output', 'successors', 'parent', 'input_to_parent']

    def __init__(self, parent=None):
        MooreNode._id_counter += 1
        self.id = MooreNode._id_counter
        self.output = None
        self.successors = {}
        self.parent = parent
        self.input_to_parent = None

    def __hash__(self):
        return hash(self.id)

    def add_successor(self, input_val, output_val, successor_node):
        """ Adds a successor node to the current node based on input """
        self.successors[input_val] = successor_node
        self.successors[input_val].output = output_val

    def get_successor(self, input_val):
        """ Returns the successor node for the given input """
        if input_val in self.successors:
            return self.successors[input_val]
        return None

    def extend_and_get(self, inp, output):
        """ Extend the node with a new successor and return the successor node """
        if inp in self.successors:
            return self.successors[inp]
        successor_node = MooreNode(parent=self)
        self.add_successor(inp, output, successor_node)
        successor_node.input_to_parent = inp
        return successor_node

    @property
    def id_counter(self):
        return self._id_counter
    
    def __str__(self):
        compactCounterExamples = True
        if compactCounterExamples and self.output==None and len(self.successors) == 1:
            #skip printing this node and print the child instead.
            succesor = list(self.successors.values())[0]
            result = str(succesor)
            return result
        else:
            inputs = []
            current_node = self
            while not current_node.parent is None:
                inputs.insert(0, current_node.input_to_parent)
                current_node = current_node.parent

            result = "node " + str(inputs) + " / " + str(self.output)
            for input_val, succesor in self.successors.items():
                result += "\n" + str(input_val) + ":\n"
                result += "\t" + str(succesor).replace("\n", "\n\t")
            return result

    def __lt__(self, other):
        return False


class Apartness:
    @staticmethod
    def incompatible_output(output1, output2):
        return output1 != output2 and \
            output1 is not None and \
            output2 is not None and \
            output1 != "unknown" and \
            output2 != "unknown"
    
    @staticmethod
    def compute_witness(state1, state2, ob_tree):
        # Finds a distinguishing sequence between two states if they are apart based on the observation tree
        if ob_tree.automaton_type == 'mealy':
            state1_destination = Apartness._show_states_are_apart_mealy(
                state1, state2, ob_tree.alphabet)
        else:
            state1_destination = Apartness._show_states_are_apart_moore(
                state1, state2, ob_tree.alphabet)
        if not state1_destination:
            return
        return ob_tree.get_transfer_sequence(state1, state1_destination)

    @staticmethod
    def states_are_apart(state1, state2, ob_tree):
        # Checks if two states are apart by checking any output difference in the observation tree
        if ob_tree.automaton_type == 'mealy':
            return Apartness._show_states_are_apart_mealy(state1, state2, ob_tree.alphabet) is not None
        else:
            return Apartness._show_states_are_apart_moore(state1, state2, ob_tree.alphabet) is not None

    @staticmethod
    def _show_states_are_apart_mealy(first, second, alphabet):
        # Identifies if two states can be distinguished by any input-output pair in the provided alphabet
        pairs = deque([(first, second)])

        while pairs:
            first_node, second_node = pairs.popleft()
            for input_val in alphabet:
                first_output = first_node.get_output(input_val)
                second_output = second_node.get_output(input_val)

                if first_output is not None and second_output is not None:
                    if first_output != second_output and (first_output not in ["unknown", None] and second_output not in ["unknown", None]):
                        return first_node.get_successor(input_val)

                    pairs.append((first_node.get_successor(
                        input_val), second_node.get_successor(input_val)))

        return None

    @staticmethod
    def _show_states_are_apart_moore(first, second, alphabet):
        # Identifies if two states can be distinguished by any input-output pair in the provided alphabet
        pairs = deque([(first, second)])
        while pairs:
            first_node, second_node = pairs.popleft()
            if first_node is not None and second_node is not None:
                first_output = first_node.output
                second_output = second_node.output
                if first_output != second_output and (first_output not in ["unknown", None] and second_output not in ["unknown", None]):
                    return first_node

                for input_val in alphabet:
                    pairs.append((first_node.get_successor(
                        input_val), second_node.get_successor(input_val)))

        return None

    @staticmethod
    def clone_subtree(node, visited=None):
        if visited is None:
            visited = {}
        if node in visited:
            return visited[node]
        # Assume node has .output and .successors
        new_node = MooreNode()
        visited[node] = new_node
        new_node.successors = {}
        for k, v in node.successors.items():
            new_node.successors[k] = Apartness.clone_subtree(v, visited)
            new_node.successors[k].parent = new_node
            new_node.successors[k].input_to_parent = k
        new_node.output = node.output
        return new_node

    @staticmethod
    def get_successors(node, input_val):
        for input in input_val:
            if node is None:
                return None
            node = node.get_successor(input)
        return node
        

    @staticmethod
    def states_are_incompatible(first, second, ob_tree):
        # Get the input to the nodes
        first_input = ob_tree.get_access_sequence(first)
        second_input = ob_tree.get_access_sequence(second)
        # Instead of deepcopy, reconstruct only the relevant subtrees
        
        root = Apartness.clone_subtree(ob_tree.root)
        first_node = Apartness.get_successors(root, first_input)
        second_node = Apartness.get_successors(root, second_input)
        result = Apartness.merge(first_node, second_node)
        # print(result, Apartness.states_are_apart(first, second, ob_tree))
        if result != Apartness.states_are_apart(first, second, ob_tree):
            print("Difference!")
        return result

    @staticmethod
    def merge(first, second):
        # Merge the second node into the first node, and return whether there is a conflict
        if first.output == "unknown" or first.output is None:
            first.output = second.output
        elif (second.output != "unknown" and second.output is not None) and first.output != second.output:
            return True

        keys = list(second.successors.keys())
        for input_val in keys:
            if input_val in first.successors:
                conflict = Apartness.merge(first.successors[input_val], second.successors[input_val])
                if conflict:
                    return True
            else:
                first.successors[input_val] = second.successors[input_val]
        return False

    @staticmethod
    def test_merge():
        from .ObservationTree import MooreNode, MealyNode
        s = MooreNode()
        t = MooreNode()
        r = MooreNode()
        q = MooreNode()
        p = MooreNode()
        p.add_successor('a', False, s)
        p.add_successor('b', True, q)
        q.add_successor('b', True, r)
        r.add_successor('a', True, t)
        # print(p)
        print(Apartness._show_states_are_apart_moore(p, q, ['a', 'b']))
        print(Apartness.merge(p, q))
        # print(p)
    
    @staticmethod
    def _get_distinguishing_sequences(group, ob_tree):
        if ob_tree.automaton_type=="mealy":
            return Apartness._get_distinguishing_sequences_mealy(group, ob_tree.alphabet)
        else:
            return Apartness._get_distinguishing_sequences_moore(group, ob_tree.alphabet)

    @staticmethod
    def _get_distinguishing_sequences_mealy(group, alphabet):
        # Identifies all distinguishing input-output pairs in the provided alphabet of the n states
        groups = deque([([], group)])

        while groups:
            access_seq, group = groups.popleft()
            for input_val in alphabet:
                #node.get_output
                valid_group = [node for node in group if node.get_output(input_val) is not None]

                if len(valid_group)>=2:
                    outputs = set([node.get_output(input_val) for node in valid_group])
                    if "unknown" in outputs:
                        outputs.remove("unknown")
                    if None in outputs:
                        outputs.remove(None)
                    if len(outputs)>=2:
                        yield access_seq + [input_val]
                    
                    groups.append((access_seq + [input_val], [node.get_successor(input_val) for node in valid_group]))

    @staticmethod
    def _get_distinguishing_sequences_moore(group, alphabet):
        # Identifies if two states can be distinguished by any input-output pair in the provided alphabet
        groups = deque([([], group)])

        while groups:
            access_seq, group = groups.popleft()
            valid_group = [node for node in group if node is not None]
            if len(valid_group)>=2:
                outputs = set([node.output for node in valid_group])
                if "unknown" in outputs:
                    outputs.remove("unknown")
                if None in outputs:
                    outputs.remove(None)
                if len(outputs)>=2:
                    yield access_seq

                for input_val in alphabet:
                    groups.append((access_seq + [input_val], [node.get_successor(input_val) for node in valid_group]))

    @staticmethod
    def compute_witness_in_tree_and_hypothesis_states(ob_tree, ob_tree_state, hyp_state):
        """
        Determines if the observation tree and the hypothesis are distinguishable based on their state outputs
        """
        if ob_tree.automaton_type == 'mealy':
            return Apartness.compute_witness_in_tree_and_hypothesis_states_mealy(ob_tree, ob_tree_state, hyp_state)
        else:
            return Apartness.compute_witness_in_tree_and_hypothesis_states_moore(ob_tree, ob_tree_state, hyp_state)

    @staticmethod
    def compute_witness_in_tree_and_hypothesis_states_mealy(ob_tree, ob_tree_state, hyp_state):
        """
        Determines if the observation tree and the hypothesis are distinguishable based on their state outputs
        """
        pairs = deque([(ob_tree_state, hyp_state)])

        while pairs:
            tree_state, hyp_state = pairs.popleft()

            for input_val in ob_tree.alphabet:
                tree_output = tree_state.get_output(input_val)

                if tree_output is not None and input_val in hyp_state.output_fun:
                    hyp_output = hyp_state.output_fun[input_val]
                    if tree_output != hyp_output and tree_output not in ["unknown", None]:
                        tree_dest = tree_state.get_successor(input_val)
                        return ob_tree.get_transfer_sequence(ob_tree_state, tree_dest)

                    pairs.append((tree_state.get_successor(
                        input_val), hyp_state.transitions[input_val]))

        return None

    @staticmethod
    def compute_witness_in_tree_and_hypothesis_states_moore(ob_tree, ob_tree_state, hyp_state):
        """
        Determines if the observation tree and the hypothesis are distinguishable based on their state outputs
        """
        pairs = deque([(ob_tree_state, hyp_state)])

        while pairs:
            tree_state, hyp_state = pairs.popleft()
            if (tree_state is not None) and (hyp_state is not None):
                tree_output = tree_state.output
                if ob_tree.automaton_type == 'dfa':
                    hyp_output = hyp_state.is_accepting
                else:
                    hyp_output = hyp_state.output

                # print(tree_output, hyp_output)
                if tree_output != hyp_output and tree_output not in ["unknown", None]:
                    # print(type(tree_output), type(hyp_output))
                    # print("Distinguishing outputs:", tree_output, hyp_output)
                    return ob_tree.get_transfer_sequence(ob_tree_state, tree_state)

                for input_val in ob_tree.alphabet:
                    if input_val in hyp_state.transitions:
                        pairs.append((tree_state.get_successor(
                            input_val), hyp_state.transitions[input_val]))

        return None
