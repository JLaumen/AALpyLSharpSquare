import csv
import os
import statistics

def analyze_and_average(csv_path, prefix):
    fields = [
        'learning_time',
        'learning_rounds',
        'queries_learning',
        'validity_query',
        'rule1',
        'rule2',
        'rule3',
        'rule4',
    ]
    sums = {k: 0.0 for k in fields}
    values = {k: [] for k in fields}
    count = 0
    with open(csv_path, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            if row['file name'].startswith(prefix) and row['automaton_size'] == "10":
                sums['learning_time'] += float(row['learning_time'])
                sums['learning_rounds'] += int(row['learning_rounds'])
                sums['queries_learning'] += int(row['queries_learning'])
                sums['validity_query'] += int(row['validity_query'])
                sums['rule1'] += int(row['rule1'])
                sums['rule2'] += int(row['rule2'])
                sums['rule3'] += int(row['rule3'])
                sums['rule4'] += int(row['rule4'])
                values['learning_time'].append(float(row['learning_time']))
                values['learning_rounds'].append(int(row['learning_rounds']))
                values['queries_learning'].append(int(row['queries_learning']))
                values['validity_query'].append(int(row['validity_query']))
                values['rule1'].append(int(row['rule1']))
                values['rule2'].append(int(row['rule2']))
                values['rule3'].append(int(row['rule3']))
                values['rule4'].append(int(row['rule4']))
                count += 1
    if count == 0:
        return None
    averages = {k: v / count for k, v in sums.items()}
    medians = {k: statistics.median(values[k]) for k in fields}
    return averages, medians, count

def print_column_differences(file1, file2, column):
    with open(file1, newline='') as f1, open(file2, newline='') as f2:
        reader1 = csv.DictReader(f1)
        reader2 = csv.DictReader(f2)
        rows1 = list(reader1)
        rows2 = list(reader2)
        min_len = min(len(rows1), len(rows2))
        total_difference = 0
        for i in range(min_len):
            val1 = rows1[i].get(column)
            val2 = rows2[i].get(column)
            if val1 != val2:
                print(f"Line {i+1}: {column} differs ({val1} vs {val2}), ({int(val1) - int(val2)})")
                total_difference += int(val1) - int(val2)
        print(f"Total difference in {column} for files {os.path.basename(file1)} and {os.path.basename(file2)}: {total_difference}")
        if len(rows1) != len(rows2):
            print(f"Files have different number of rows: {len(rows1)} vs {len(rows2)}")

if __name__ == "__main__":
    folder = 'Benchmarking/incomplete_dfa_benchmark'
    prefix = 'oliveira/'
    csv_files = [
        os.path.join(folder, 'benchmark4.csv'),
        os.path.join(folder, 'benchmark5.csv')
    ]
    for csv_file in csv_files:
        if os.path.exists(csv_file):
            result = analyze_and_average(csv_file, prefix)
            if result:
                averages, medians, count = result
                print(f"\nAverages from {os.path.basename(csv_file)} ({count} files):")
                print(f"learning_time: {averages['learning_time']:.3f}")
                print(f"learning_rounds: {averages['learning_rounds']:.3f}")
                print(f"queries_learning: {averages['queries_learning']:.3f}")
                print(f"validity_query: {averages['validity_query']:.3f}")
                print(f"rule1: {averages['rule1']:.3f}")
                print(f"rule2: {averages['rule2']:.3f}")
                print(f"rule3: {averages['rule3']:.3f}")
                print(f"rule4: {averages['rule4']:.3f}")
                print(f"Medians from {os.path.basename(csv_file)} ({count} files):")
                print(f"learning_time: {medians['learning_time']:.3f}")
                print(f"learning_rounds: {medians['learning_rounds']:.3f}")
                print(f"queries_learning: {medians['queries_learning']:.3f}")
                print(f"validity_query: {medians['validity_query']:.3f}")
                print(f"rule1: {medians['rule1']:.3f}")
                print(f"rule2: {medians['rule2']:.3f}")
                print(f"rule3: {medians['rule3']:.3f}")
                print(f"rule4: {medians['rule4']:.3f}")
            else:
                print(f"No matching rows in {csv_file}")
        else:
            print(f"File not found: {csv_file}")
    column = 'queries_learning'
    if all(os.path.exists(f) for f in csv_files):
        print_column_differences(csv_files[0], csv_files[1], column)
