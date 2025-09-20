import csv
import os
import statistics

def analyze_and_average(csv_file):
    with open(csv_file, newline='') as f:
        reader = csv.DictReader(f)
        data = list(reader)

    grouped = {}
    for row in data:
        size = int(row['automaton_size'])
        grouped.setdefault(size, []).append(row)

    for size, rows in grouped.items():
        total_times = [float(r['total_time']) for r in rows]
        analyzed_bases = [float(r['analyzed_bases']) for r in rows]
        print(f"Automaton size: {size}")
        print(f"  Number of benchmarks: {len(rows)}")
        print(f"  Mean total_time: {statistics.mean(total_times):.4f}")
        print(f"  Median total_time: {statistics.median(total_times):.4f}")
        print(f"  Mean analyzed_bases: {statistics.mean(analyzed_bases):.4f}")

if __name__ == "__main__":
    folder = 'Benchmarking/incomplete_dfa_benchmark'
    prefix = 'oliveira/'
    csv_files = [
        os.path.join(folder, 'benchmark_04_11.csv')
    ]
    for csv_file in csv_files:
        if os.path.exists(csv_file):
            result = analyze_and_average(csv_file)

        else:
            print(f"File not found: {csv_file}")

