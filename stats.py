import csv
import os
import statistics

def analyze_and_average(csv_file):
    with open(csv_file, newline='') as f:
        reader = csv.DictReader(f)
        data = list(reader)

    grouped = {}
    for row in data:
        # if row.get('succeeded', 'true').lower() == 'true':
        size = int(row['automaton_size'])
        grouped.setdefault(size, []).append(row)

    for size, rows in grouped.items():
        # if size < 10:
        #     continue
        total_times = [float(r['total_time']) for r in rows]
        analyzed_bases = [float(r['analyzed_bases']) for r in rows]
        queries = [int(r['queries_learning']) for r in rows]
        validity = [int(r['validity_query']) for r in rows]
        print(f"Automaton size: {size}")
        print(f"  Number of benchmarks: {len(rows)}")
        print(f"  Mean total_time: {statistics.mean(total_times):.4f}")
        print(f"  Median total_time: {statistics.median(total_times):.4f}")
        print(f"  Mean analyzed_bases: {statistics.mean(analyzed_bases):.4f}")
        print(f"  Median analyzed_bases: {statistics.median(analyzed_bases):.4f}")
        print(f"  Mean queries_learning: {statistics.mean(queries):.2f}")
        print(f"  Median queries_learning: {statistics.median(queries):.2f}")
        print(f"  Mean validity_query: {statistics.mean(validity):.2f}")
        print(f"  Median validity_query: {statistics.median(validity):.2f}")

if __name__ == "__main__":
    folder = 'Benchmarking/incomplete_dfa_benchmark'
    prefix = 'oliveira/'
    csv_files = [
        # os.path.join(folder, 'benchmark_apart_pessimistic_1000_04_11.csv'),
        os.path.join(folder, 'benchmark_apart_optimistic_1000_04_11.csv'),
    ]
    for csv_file in csv_files:
        if os.path.exists(csv_file):
            print(f"Analyzing file: {csv_file}")
            analyze_and_average(csv_file)
        else:
            print(f"File not found: {csv_file}")

