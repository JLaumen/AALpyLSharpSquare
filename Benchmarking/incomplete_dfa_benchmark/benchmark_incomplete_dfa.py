import os

from aalpy.SULs import IncompleteDfaSUL
from aalpy.oracles import ValidityDataOracle
from aalpy.learning_algs import run_LsharpSquare
from aalpy.utils.HelperFunctions import print_learning_info

'''
in the aalpy folder
run using:
PYTHONPATH=. python3 Benchmarking/incomplete_dfa_benchmark/benchmark_incomplete_dfa.py
'''


testCasesPath = "Benchmarking/incomplete_dfa_benchmark/test_cases/"

def is_simple_input(input): 
    for i in input:
        if i not in ["0", "1", "X"]:
            return False
    return True

def get_possible_words(prefix:list, suffix:list, alphabet:list) -> list:
    words = []
    if suffix:
        if suffix[0] == "X": 
            for input_val in alphabet:
                words.extend(get_possible_words(prefix + [input_val], suffix[1:], alphabet))
        else:
            input_val = suffix[0]
            words.extend(get_possible_words(prefix + [input_val], suffix[1:], alphabet))
        return words
    else:
        return [prefix]

def parse_file(filename:str, alphabet:list):
    f = open(testCasesPath + filename)
    known_words = []
    observedAlphabet = []
    for l in f:
        splitIndex = l.strip().rfind(',')
        input, output = l.strip()[:splitIndex], l.strip()[splitIndex+1:]
        output = {"+" : True, "-" : False}[output.strip()]
        if is_simple_input(input):
            inputs = get_possible_words([], input, alphabet)
            for word in inputs:
                for let in word:
                    if not let in observedAlphabet:
                        observedAlphabet.append(let)
                known_words.append((word, output))
        else: 
            word = input.split(";")
            for let in word:
                if not let in observedAlphabet:
                    observedAlphabet.append(let)
            known_words.append((word, output))
    
    return known_words, observedAlphabet


def run_test_case(filename:str, print_level=0):
    alphabet = ["0", "1"]
    data, alphabet = parse_file(filename, alphabet)
    '''print("alphabet:")
    for i in alphabet:
        print(i)'''
    sul = IncompleteDfaSUL(data.copy(), fractionKnown=0) #, "random", fractionKnown=0.5)
    eq_oracle = ValidityDataOracle(data.copy())

    learned_dfa, info = run_LsharpSquare(alphabet, sul, eq_oracle, automaton_type='dfa', max_learning_rounds=60, 
                            print_level=print_level-1, return_data=True)

    if print_level>0:
        print(learned_dfa)
    successful = eq_oracle.find_cex(learned_dfa) == None
    info["successful"] = successful
    return info


def run_test_cases():
    output_file = open("Benchmarking/incomplete_dfa_benchmark/output.csv", "w")
    output_file.write("file name,succeeded,learning_rounds,automaton_size,learning_time,smt_time,eq_oracle_time,total_time,queries_learning,validity_query,rule1,rule2,rule3,rule4,nodes,informative_nodes,analyzed_bases,sul_steps,cache_saved,queries_eq_oracle,steps_eq_oracle\n")
    #lee alpharegex 
    LeeAlpharegex = testCasesPath + "/lee_alpharegex"
    for num in range(1, 26):
        if num in [9]:
            continue
        print("lee_alpharegex/" + str(num))
        info = run_test_case("lee_alpharegex/" + str(num))
        output_file.write(','.join(["lee_alpharegex/" + str(num), 
                                    str(info['successful']),
                                    str(info['learning_rounds']),
                                    str(info['automaton_size']),
                                    str(info['learning_time']),
                                    str(info['smt_time']),
                                    str(info['eq_oracle_time']),
                                    str(info['total_time']),
                                    str(info['queries_learning']),
                                    str(info['validity_query']),
                                    str(info['rule1']),
                                    str(info['rule2']),
                                    str(info['rule3']),
                                    str(info['rule4']),
                                    str(info['nodes']),
                                    str(info['informative_nodes']),
                                    str(info['analyzed_bases']),
                                    str(info['sul_steps']),
                                    str(info['cache_saved']),
                                    str(info['queries_eq_oracle']),
                                    str(info['steps_eq_oracle'])]) + "\n")
    Oliveira = testCasesPath + "/oliveira"
    for folder_name in sorted(os.listdir(Oliveira)):
        if folder_name in [".DS_Store", 's12', 's13']:
            continue
        for file_name in sorted(os.listdir(Oliveira + "/" + folder_name)):
            if "oliveira/" + folder_name + "/" + file_name in [
                
            ]:
                continue
            print("oliveira/" + folder_name + "/" + file_name)
            info = run_test_case("oliveira/" + folder_name + "/" + file_name)
            output_file.write(','.join(["oliveira/" + folder_name + "/" + file_name, 
                                    str(info['successful']),
                                    str(info['learning_rounds']),
                                    str(info['automaton_size']),
                                    str(info['learning_time']),
                                    str(info['smt_time']),
                                    str(info['eq_oracle_time']),
                                    str(info['total_time']),
                                    str(info['queries_learning']),
                                    str(info['validity_query']),
                                    str(info['rule1']),
                                    str(info['rule2']),
                                    str(info['rule3']),
                                    str(info['rule4']),
                                    str(info['nodes']),
                                    str(info['informative_nodes']),
                                    str(info['analyzed_bases']),
                                    str(info['sul_steps']),
                                    str(info['cache_saved']),
                                    str(info['queries_eq_oracle']),
                                    str(info['steps_eq_oracle'])]) + "\n")
    output_file.close()

def run_test_cases_specific(test_files):
    output_file = open("Benchmarking/incomplete_dfa_benchmark/output.csv", "w")
    output_file.write("file name,succeeded,learning_rounds,automaton_size,learning_time,smt_time,eq_oracle_time,total_time,queries_learning,validity_query,rule1,rule2,rule3,rule4,nodes,informative_nodes,analyzed_bases,sul_steps,cache_saved,queries_eq_oracle,steps_eq_oracle\n")
    
    for file_name in test_files:
        print(file_name)
        info = run_test_case(file_name, print_level=4)
        output_file.write(','.join([file_name, 
                                str(info['successful']),
                                str(info['learning_rounds']),
                                str(info['automaton_size']),
                                str(info['learning_time']),
                                str(info['smt_time']),
                                str(info['eq_oracle_time']),
                                str(info['total_time']),
                                str(info['queries_learning']),
                                str(info['validity_query']),
                                str(info['rule1']),
                                str(info['rule2']),
                                str(info['rule3']),
                                str(info['rule4']),
                                str(info['nodes']),
                                str(info['informative_nodes']),
                                str(info['analyzed_bases']),
                                str(info['sul_steps']),
                                str(info['cache_saved']),
                                str(info['queries_eq_oracle']),
                                str(info['steps_eq_oracle'])]) + "\n")
    output_file.close()


#run_test_cases()
run_test_cases_specific(["oliveira/04_11/randm11.02.02.19.020_0030.05.aba.beta",
                       "oliveira/s11/randm11.02.02.19.020_0030.05.aba.beta",
                       "oliveira/04_11/randm11.02.02.19.020_0030.02.aba.beta"])
#run_test_cases_specific(["lee_alpharegex/1"])
#run_test_case("oliveira/04_11/randm11.02.02.19.020_0030.05.aba.beta", print_level=4)
#run_test_case("oliveira/04_09/randm09.02.02.01.020_0030.03.aba.beta", print_level=4)
#info = run_test_case("oliveira/04_07/randm05.02.02.13.020_0030.02.aba.beta", print_level=4)
#info = run_test_case("learning-benchmarks/SnL16.txt", print_level=4)
#print(info['successful'])
#run_test_case("lee_alpharegex/1", print_level=4)
#run_test_case("oliveira/04_07/randm07.02.02.18.020_0030.01.aba.beta", print_level=4)
