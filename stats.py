import csv
import os
import statistics
import matplotlib.pyplot as plt

def plot_queries_vs_size(csv_files, output=None):

    # collect queries per size for each input CSV separately
    file_dicts = []
    for csv_file in csv_files:
        sizes_to_queries = {}
        if not os.path.exists(csv_file):
            print(f"File not found: {csv_file}")
            file_dicts.append(sizes_to_queries)
            continue
        with open(csv_file, newline='') as f:
            reader = csv.DictReader(f)
            for r in reader:
                try:
                    size = int(r['automaton_size'])
                    q = int(r['queries_learning'])
                except (KeyError, ValueError):
                    continue
                sizes_to_queries.setdefault(size, []).append(q)
        file_dicts.append(sizes_to_queries)

    if not any(d for d in file_dicts):
        print("No data to plot")
        return

    # union of sizes across all files, sorted
    sizes = sorted({s for d in file_dicts for s in d.keys()})

    # make plot a bit wider and taller to accommodate larger violins
    plt.figure(figsize=(max(12, len(sizes) * 0.9), 7))

    # colors for each input CSV (will cycle if more than provided)
    colors = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728']
    n_files = len(file_dicts)

    # horizontal offsets so violins for the same size don't overlap
    default_spacing = 0.40  # default spacing between multiple-file violins at same size
    # use a smaller spacing when exactly two files so the pair appears closer together
    spacing = 0.22 if n_files == 2 else default_spacing
    offsets = [ (i - (n_files - 1) / 2) * spacing for i in range(n_files) ]

    # create violins per file, only where data exists
    from matplotlib.patches import Patch
    legend_handles = []
    for i, fd in enumerate(file_dicts):
        positions = []
        data = []
        for s in sizes:
            vals = fd.get(s)
            if not vals:
                continue
            positions.append(s + offsets[i])
            data.append(vals)
        if not data:
            continue
        # make violins slightly smaller so there's more space between DFA sizes
        # when we reduced spacing for two files, make violins a bit wider relative to spacing
        violin_width = spacing * 1.5
        parts = plt.violinplot(data, positions=positions, widths=violin_width, showmeans=False, showmedians=True)
        for pc in parts['bodies']:
            pc.set_facecolor(colors[i % len(colors)])
            pc.set_edgecolor('black')
            pc.set_linewidth(0.7)
            pc.set_alpha(0.8)
        if 'cmedians' in parts and parts['cmedians'] is not None:
            parts['cmedians'].set_color('black')
            try:
                parts['cmedians'].set_linewidth(2.0)
            except Exception:
                pass
        # set explicit labels for first two files
        if csv_files and i < len(csv_files):
            if i == 0:
                label = 'Pessimistic'
            elif i == 1:
                label = 'Optimistic'
            else:
                label = os.path.basename(csv_files[i])
        else:
            label = f'file_{i}'
        legend_handles.append(Patch(facecolor=colors[i % len(colors)], edgecolor='black', label=label))

    plt.xlabel('DFA Size')
    plt.ylabel('Membership Queries')
    plt.yscale('log')
    plt.title('Queries vs Automaton Size (violin)')

    # show horizontal and vertical grid lines (vertical lines on DFA sizes)
    plt.grid(True, axis='y', linestyle='--', linewidth=0.5, alpha=0.6)
    plt.grid(True, axis='x', linestyle='--', linewidth=0.5, alpha=0.4)

    # ensure there is a tick for every DFA size
    plt.xticks(sizes)

    # optional: small margin so violins are fully visible
    if sizes:
        plt.xlim(min(sizes) - 0.6, max(sizes) + 0.6)

    if legend_handles:
        plt.legend(handles=legend_handles, loc='upper left')

    if output:
        plt.savefig(output, bbox_inches='tight')
        print(f"Saved plot to {output}")
    else:
        plt.show()

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
        print(f"  Mean total_time: {statistics.mean(total_times):.2f}")
        print(f"  Median total_time: {statistics.median(total_times):.2f}")
        print(f"  Mean analyzed_bases: {statistics.mean(analyzed_bases):.2f}")
        print(f"  Median analyzed_bases: {statistics.median(analyzed_bases):.2f}")
        print(f"  Mean queries_learning: {statistics.mean(queries):.2f}")
        print(f"  Median queries_learning: {statistics.median(queries):.2f}")
        print(f"  Mean validity_query: {statistics.mean(validity):.2f}")
        print(f"  Median validity_query: {statistics.median(validity):.2f}")

if __name__ == "__main__":
    folder = 'Benchmarking/incomplete_dfa_benchmark'
    prefix = 'oliveira/'
    csv_files = [
        os.path.join(folder, 'benchmark_apart_pessimistic_1000_04_12.csv'),
        os.path.join(folder, 'benchmark_apart_optimistic_1000_04_12.csv'),
    ]
    for csv_file in csv_files:
        if os.path.exists(csv_file):
            print(f"Analyzing file: {csv_file}")
            analyze_and_average(csv_file)
        else:
            print(f"File not found: {csv_file}")
    plot_queries_vs_size(csv_files, output="plot1.png")
