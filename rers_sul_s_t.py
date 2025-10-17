from aalpy.base import SUL
from aalpy.base.SUL import CacheSUL
from aalpy.utils import load_automaton_from_file, make_input_complete, save_automaton_to_file
from aalpy.automata import MealyMachine
import os
import subprocess
import argparse
from data.alphabet import alphabet


class RERSSULST(SUL):
    def __init__(self, benchmark, t_type, for_T=True, is_prefix_closed=True, is_suffix_closed=False, debug=False):
        super().__init__()
        self.state = None
        self.hash = None
        self.already_rejected = False
        self.already_accepted = False
        self.already_none = False
        self.for_T = for_T
        self.is_prefix_closed = is_prefix_closed  # for T
        self.is_suffix_closed = is_suffix_closed  # for B
        self.memory = {}
        self.in_system_memory = {}
        self.benchmark = benchmark
        self.debug = debug
        if benchmark in ["m135", "m158",  "m159", "m164", "m172", "m181", "m183", "m185", "m201", "m24", "m45", "m54", "m55", "m76", "m95"]:
            self.cwd = "rers2019/IndReachabilityRers2019/arithmetic/" + benchmark
        elif benchmark in ["m106", "m131", "m132", "m167", "m173", "m182", "m189", "m190", "m196", "m199", "m22", "m27", "m41", "m49", "m65"]:
            self.cwd = "rers2019/IndReachabilityRers2019/data-structures/" + benchmark
        else:
            raise ValueError("Unknown benchmark")
        self.t_type = t_type
        if self.t_type in ["3", "5"]:
            self.cwd = "rers2019/IndReachabilityRers2019"
            self.class_name = 'DelayWrapper'
        else:
            self.class_name = self.benchmark + '_Reach'
        # with open(f"{self.cwd}/{self.benchmark}_Reach.java") as f:
        #     data = f.read()
        #     a = data.find("String[] inputs = {")
        #     l_str = data[a + len("String[] inputs = {"):data.find("}", a)]
        #     self.alphabet = l_str.replace('"', "").split(",")
        self.alphabet = alphabet.get(benchmark, [])
        if self.t_type in ["3", "5"]:
            self.alphabet += ["assert"]
        if len(self.alphabet) == 0 and not self.debug:
            raise ValueError("Empty alphabet")
        self.system_steps = 0
        self.system_inits = 0
        self.steps_since_last_init = 0
        self.system_steps_knowing_s = 0
        self.system_inits_knowing_s = 0
        self.steps_since_last_init_knowing_s = 0
        self.init_state = None
        self.init_hash = None

    def compute_init(self):
        if self.steps_since_last_init > 0:
            self.system_inits += 1
            self.steps_since_last_init = 0
        if self.steps_since_last_init_knowing_s > 0:
            self.system_inits_knowing_s += 1
            self.steps_since_last_init_knowing_s = 0
        if self.init_state is not None:
            return self.init_state, self.init_hash

        process = subprocess.Popen(
            ['java', self.class_name],  # Name of the compiled Java class (without .class extension)
            stdin=subprocess.PIPE,  # Pipe to send input to the program
            stdout=subprocess.PIPE,  # Pipe to capture output
            stderr=subprocess.PIPE,  # Pipe to capture error (if any)
            text=True,  # Treat input and output as strings (instead of bytes)
            cwd=self.cwd
            # Set the working directory where the Java class is located
        )
        # Send input to the Java program and capture the output
        if self.t_type in ["3", "5"]:
            stdout, stderr = process.communicate(self.benchmark + "\n" + "init")
        else:
            stdout, stderr = process.communicate("init" + "\n")
        state, new_hash = stdout.rstrip().split("\n")
        process.terminate()
        self.init_state, self.init_hash = state, new_hash
        return state, new_hash

    def compute_transition(self, s, a):
        self.system_steps += 1
        self.steps_since_last_init += 1

        if (s, a) in self.memory:
            output, new_state, new_hash, in_T = self.memory[(s, a)]
        elif s == "error":
            output, new_state, new_hash, in_T = "error", "error", "error", "Legal"
        else:
            process = subprocess.Popen(
                ['java', self.class_name],  # Name of the compiled Java class (without .class extension)
                stdin=subprocess.PIPE,  # Pipe to send input to the program
                stdout=subprocess.PIPE,  # Pipe to capture output
                stderr=subprocess.PIPE,  # Pipe to capture error (if any)
                text=True,  # Treat input and output as strings (instead of bytes)
                cwd=self.cwd
                # Set the working directory where the Java class is located
            )
            # Send input to the Java program and capture the output
            if self.t_type in ["3", "5"]:
                stdout, stderr = process.communicate(self.benchmark + "\n" + s + "\n" + a)
            else:
                stdout, stderr = process.communicate(s + "\n" + a)
            # print(stdout)
            # print(stderr)
            outputs = stdout.rstrip().split("\n")
            if len(outputs) == 4:
                output, new_state, new_hash, in_T = outputs
            else:
                output = ""
                try:
                    new_state, new_hash, in_T = stdout.rstrip().split("\n")
                except ValueError:
                    raise ValueError(a)
            process.terminate()
            self.memory[(s, a)] = (output, new_state, new_hash, in_T)
            if new_hash not in self.in_system_memory:
                self.in_system_memory[new_hash] = (in_T, output)

        if in_T == "Legal":
            self.system_steps_knowing_s += 1
            self.steps_since_last_init_knowing_s += 1
        return output, new_state, new_hash, in_T

    def query(self, word: tuple) -> list:
        self.pre()
        if len(word) == 0:
            if self.for_T:
                out = [True]
            else:
                out = [False]
        else:
            out = [self.step(letter) for letter in word]
        self.post()
        return out

    def pre(self):
        self.state, self.hash = self.compute_init()
        if self.for_T:
            self.already_rejected = False
            self.already_accepted = True
        else:
            self.already_rejected = True
            self.already_accepted = False
            self.already_none = False

    def post(self):
        self.state = None
        self.hash = None
        self.already_rejected = False
        self.already_accepted = False
        self.already_none = False

    def step(self, letter):
        if self.for_T:
            if self.is_prefix_closed and self.already_rejected:
                return False
        output, new_state, new_hash, in_T = self.compute_transition(self.state, letter)
        if self.t_type in ["3", "5"] and letter == "assert":
            if self.hash is not None and self.in_system_memory[self.hash][0] == "Legal":
                in_T = "Legal"
            if self.hash is not None and self.in_system_memory[self.hash][1] == "_none_" and new_state[0] == "3":
                output = "error"
        self.state = new_state
        self.hash = new_hash
        if self.for_T:
            if in_T != "Legal":
                self.already_rejected = True
            return in_T == "Legal"
        else:
            if output == "error":
                self.already_accepted = True
            if in_T != "Legal":
                self.already_none = True
            if self.already_none:
                return None
            return self.already_accepted  # maybe we need to change this to "error" == output




if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--benchmark', '-B', type=str, default="m45")
    parser.add_argument('--discover', '-D', type=str, default="T")
    parser.add_argument('--walks_per_state', '-W', type=int, default=10)
    parser.add_argument('--walk_len', '-L', type=int, default=5)
    args = parser.parse_args()

    sul = CacheSUL(RERSSULST(benchmark="m45", for_T=False, is_prefix_closed=False, is_suffix_closed=False))
    print(sul.query(['ai2_ce3', 'usr2_ai2_VoidReply', 'usr3_ai1_re1', 'usr1_ni1_ne1', 'ai3_ce2']))
    # print(sul.query(['ai2_ce3', 'usr2_ai2_VoidReply', 'usr3_ai1_re1', 'usr1_ni1_ne1', 'ai1_ce1']))

    # if args.discover == "T":
    #     sul = CacheSUL(RERSSUL(benchmark=args.benchmark, for_T=True, is_prefix_closed=True, is_suffix_closed=False))
    #     #sul = CacheSUL(RERSSUL(benchmark=args.benchmark, for_T=True, is_prefix_closed=False, is_suffix_closed=False)) # not prefix closed
    # else:
    #     sul = CacheSUL(RERSSUL(benchmark=args.benchmark, for_T=False, is_prefix_closed=False, is_suffix_closed=True))
    #
    # alphabet = sul.sul.alphabet
    # # print(len(alphabet))
    # # print(sul.query(('ai2_ce3', 'usr2_ai2_VoidReply', 'usr3_ai1_re1', 'usr1_ni1_ne1', 'ai3_ce2')))
    #
    #
    # # eq_oracle = NewBreadthFirstExplorationEqOracle(alphabet, sul, depth=4)
    # # eq_oracle = WMethodEqOracle(alphabet, sul, max_number_of_states=len(sul.sul.A.states)*2)
    # eq_oracle = RandomWMethodEqOracle(alphabet, sul, walks_per_state=args.walks_per_state, walk_len=args.walk_len)
    #
    # learned_dfa = run_Lstar(alphabet, sul, eq_oracle, automaton_type='dfa', cache_and_non_det_check=True,
    #                         cex_processing=None, print_level=3)

    # os.makedirs(f'output/{args.benchmark}', exist_ok=True)
    # save_automaton_to_file(learned_dfa, f'output/{args.benchmark}/{args.discover}.dot', 'dot')
