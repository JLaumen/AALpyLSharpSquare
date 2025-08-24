import csv
import os

def analyze_and_average(csv_path, prefix):
    sums = {
        'learning_time': 0.0,
        'learning_rounds': 0,
        'queries_learning': 0,
        'validity_query': 0,
        'rule1': 0,
        'rule2': 0,
        'rule3': 0,
        'rule4': 0,
    }
    count = 0
    with open(csv_path, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            if row['file name'].startswith(prefix):
                sums['learning_time'] += float(row['learning_time'])
                sums['learning_rounds'] += int(row['learning_rounds'])
                sums['queries_learning'] += int(row['queries_learning'])
                sums['validity_query'] += int(row['validity_query'])
                sums['rule1'] += int(row['rule1'])
                sums['rule2'] += int(row['rule2'])
                sums['rule3'] += int(row['rule3'])
                sums['rule4'] += int(row['rule4'])
                count += 1
    if count == 0:
        return None
    averages = {k: v / count for k, v in sums.items()}
    return averages, count

if __name__ == "__main__":
    folder = 'Benchmarking/incomplete_dfa_benchmark'
    prefix = 'oliveira/'
    csv_files = [
        os.path.join(folder, 'initial_benchmark.csv'),
        os.path.join(folder, 'reset.csv'),
        os.path.join(folder, 'filter.csv'),
        os.path.join(folder, 'output.csv'),
        os.path.join(folder, 'solve.csv'),
        os.path.join(folder, 'solve2.csv')
    ]
    for csv_file in csv_files:
        if os.path.exists(csv_file):
            result = analyze_and_average(csv_file, prefix)
            if result:
                averages, count = result
                print(f"\nAverages from {os.path.basename(csv_file)} ({count} files):")
                print(f"learning_time: {averages['learning_time']:.3f}")
                print(f"learning_rounds: {averages['learning_rounds']:.3f}")
                print(f"queries_learning: {averages['queries_learning']:.3f}")
                print(f"validity_query: {averages['validity_query']:.3f}")
                print(f"rule1: {averages['rule1']:.3f}")
                print(f"rule2: {averages['rule2']:.3f}")
                print(f"rule3: {averages['rule3']:.3f}")
                print(f"rule4: {averages['rule4']:.3f}")
            else:
                print(f"No matching rows in {csv_file}")
        else:
            print(f"File not found: {csv_file}")