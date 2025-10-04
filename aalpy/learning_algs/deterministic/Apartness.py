from collections import deque
from copy import deepcopy
from copy import copy
from .Nodes import *

pessimistic = False
apart = True

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
    def clone_subtree(node, access):
        new_node = MooreNode()
        new_node.access_sequence = access
        new_node.successors = {}
        for k, v in node.successors.items():
            new_node.successors[k] = Apartness.clone_subtree(v, access + [k])
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
        if apart:
            return Apartness.states_are_apart(first, second, ob_tree)

        # Assumes that a node cannot be a descendant of a node with a higher id
        if second.id < first.id:
            first, second = second, first

        if (first.id, second.id) in ob_tree.apartness_cache:
            return True

        # Checking apartness is easier than checking incompatibility,
        # so we check that first
        if Apartness.states_are_apart(first, second, ob_tree):
            ob_tree.apartness_cache.add((first.id, second.id))
            return True

        # Unfortunately, we need to clone the tree to avoid modifying it.
        # This is very slow (dominates the running time), so I am looking for a better solution.
        # It works for testing the amount of queries though.
        # The actual merging takes about the same time as the apartness checking over the course of the whole algorithm.
        first_input = ob_tree.get_access_sequence(first)
        second_input = ob_tree.get_access_sequence(second)
        root = Apartness.clone_subtree(ob_tree.root, [])
        first_node = Apartness.get_successors(root, first_input)
        second_node = Apartness.get_successors(root, second_input)

        # Try merging the two nodes, and see if there is a conflict.
        # In case of a conflict, we get the access sequences to the nodes causing the conflict
        first_access, second_access = Apartness.merge(first_node, second_node)

        if first_access is not None:
            # Incompatible!
            ob_tree.apartness_cache.add((first.id, second.id))

            # print("Conflict when merging", first.id, second.id)
            # print(first_node.access_sequence, second_node.access_sequence)
            # print(first_access, second_access)
            # print("Apartness candidates:")

            # Construct possible candidates that can prove apartness.
            # The first candidate is the transfer sequence from the first node to the first node causing the conflict
            candidate = first_access[len(first_node.access_sequence):]
            candidates = [candidate]
            # print(candidate)

            # The other candidates are given by extending the candidate while walking backwards over the tree
            # from the second node causing the conflict, until we reach the second node.
            # This assumes that the first candidate is a suffix of the second access sequence,
            # but that seems to hold.
            while candidate != second_access[len(second_node.access_sequence):]:
                candidate = [second_access[-len(candidate) - 1]] + candidate
                candidates.append(candidate)
                # print(candidate)

            # From the list of candidates, we can construct the experiments.
            # The pairs are given by simply appending the candidates to the two nodes.
            # For now, we already do the experiments here.
            # In theory, you can stop once an experiment shows apartness.
            # print("Suggested experiments:")
            for candidate in candidates:
                # print(first_node.access_sequence + candidate, second_node.access_sequence + candidate)
                res1 = ob_tree.experiment(first_node.access_sequence + candidate)
                res2 = ob_tree.experiment(second_node.access_sequence + candidate)
                # print("Experiment", res1, res2)
                # print(Apartness.states_are_apart(first, second, ob_tree))
            # if Apartness.states_are_apart(first, second, ob_tree):
            #     print("States are apart after experiments")
            return True

        # Compatible!
        return False

    @staticmethod
    def merge(first, second):
        """
        Merge the second node into the first node.
        :param first: Node to merge into
        :param second: Node to merge from
        :return: Whether there was a conflict during the merge
        """
        # print("merging", first.id, second.id)
        
        # Prevent merging a node with itself
        if first.id == second.id:
            return None, None
        
        # Update the output of the first node,
        # while ensuring local compatibility
        if first.output == "unknown" or first.output is None:
            first.output = second.output
        elif (second.output != "unknown" and second.output is not None) and first.output != second.output:
            return first.access_sequence, second.access_sequence

        # When merging two nodes, we might create a non-deterministic automaton.
        # To solve this, we first recursively merge the nodes that would create non-determinism.
        while True:
            for input_val in second.successors.keys():
                if input_val in first.successors and first.successors[input_val].id != second.successors[input_val].id:
                    # Nodes share a common successor, so we need to merge those first
                    first_access, second_access = Apartness.merge(first.successors[input_val], second.successors[input_val])
                    if first_access is not None:
                        # Merging successors led to a conflict
                        return first_access, second_access
                    break
            else:
                # No more common successors
                break

        # From this point on, we can assume that merges will not lead to a non-deterministic automaton,
        # so we can simply copy the successors from the second node to the first node.
        # Note that we don't actually use the "parent" attribute anywhere, so we don't need to update that.
        for input_val in second.successors.keys():
            first.successors[input_val] = second.successors[input_val]

        first.id = f"{first.id}+{second.id}"

        # Make second object point to first instead
        second.id = first.id
        second.output = first.output
        second.successors = first.successors
        return None, None

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
        print(p)
        print("p", p.id)
        print("q", q.id)
        print("r", r.id)
        print("s", s.id)
        print("t", t.id)
        print(r.parent)
        print(Apartness._show_states_are_apart_moore(p, q, ['a', 'b']))
        # print(Apartness.merge(p, q))
        print(Apartness.merge(q, p))
    
    @staticmethod
    def get_distinguishing_sequences(group, ob_tree):
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
        if pessimistic:
            return
        # length = 0
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
                    # if length == 0:
                    #     length = len(access_seq)
                    # elif len(access_seq)>length:
                    #     return

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
