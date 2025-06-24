#!/usr/bin/env python3
import argparse, subprocess, re, statistics, sys
from collections import defaultdict
import re

def parse_divan_output(text):
    results = []
    current_group = None

    # Match benchmark row lines
    row_re = re.compile(
        r"^[│╰├ ]*[├╰]─\s+\(([^)]+)\)\s+([\d.]+)\s*(\w+)\s+│\s+([\d.]+)\s*(\w+)\s+│\s+([\d.]+)\s*(\w+)\s+│\s+([\d.]+)\s*(\w+)\s+│\s+(\d+)\s+│\s+(\d+)"
    )
    # Match group header line
    group_re = re.compile(r"^[│╰├ ]*[├╰]─\s+([\w\d_]+)")

    lines = text.strip().splitlines()

    for line in lines:
        if '│' not in line:
            continue

        group_match = group_re.match(line)
        if group_match and '(' not in line:
            current_group = group_match.group(1).strip()
            continue

        row_match = row_re.match(line)
        if row_match:
            (case, fastest_val, fastest_unit,
             slowest_val, slowest_unit,
             median_val, median_unit,
             mean_val, mean_unit,
             samples, iters) = row_match.groups()

            def to_ns(val, unit):
                scale = {'ns': 1, 'µs': 1e3, 'us': 1e3, 'ms': 1e6}
                return float(val) * scale[unit]

            results.append({
                'group': current_group,
                'case': f'({case})',
                'fastest_ns': to_ns(fastest_val, fastest_unit),
                'slowest_ns': to_ns(slowest_val, slowest_unit),
                'median_ns': to_ns(median_val, median_unit),
                'mean_ns': to_ns(mean_val, mean_unit),
                'samples': int(samples),
                'iters': int(iters),
            })

    return results

def average_fields(records):
    grouped = defaultdict(list)

    # Group by ('group', 'case')
    for record in records:
        key = (record['group'], record['case'])
        grouped[key].append(record)

    averaged = {}

    for key, group_records in grouped.items():
        agg = {'group': key[0], 'case': key[1]}
        count = len(group_records)

        # Find all *_ns fields to average
        ns_keys = [k for k in group_records[0] if k.endswith('_ns')]
        for ns_key in ns_keys:
            total = sum(rec[ns_key] for rec in group_records)
            agg[ns_key] = total / count

        averaged[key] = agg

    return averaged

def render_divan_table(averaged_data):
    # Sort by group then case
    from collections import defaultdict

    grouped = defaultdict(list)
    for (group, case), stats in averaged_data.items():
        grouped[group].append((case, stats))

    lines = []

    # Header
    lines.append("                              fastest      │ slowest      │ median       │ mean         │ samples│ iters")

    # Content
    for group in sorted(grouped.keys()):
        lines.append(f"├─ {group:<32}        │{'':14}│{'':14}│{'':14}│{'':8}│")
        group_items = grouped[group]

        for i, (case, stats) in enumerate(sorted(group_items)):
            prefix = "│  ╰─" if i == len(group_items) - 1 else "│  ├─"

            fastest = format_ns(stats['fastest_ns'])
            slowest = format_ns(stats['slowest_ns'])
            median = format_ns(stats['median_ns'])
            mean   = format_ns(stats['mean_ns'])
            samples = stats.get('samples', 8)
            iters   = stats.get('iters', 8)

            line = f"{prefix} {case:<23} {fastest:<13}│ {slowest:<13}│ {median:<13}│ {mean:<13}│ {samples:<7}│ {iters}"
            lines.append(line)

    return "\n".join(lines)

def format_ns(ns):
    if ns > 1e6: return f"{ns/1e6:.2f} ms"
    if ns > 1e3: return f"{ns/1e3:.2f} µs"
    return f"{ns:.0f} ns"

def main():

    parser = argparse.ArgumentParser(
        description="Calls `cargo bench` multiple times and averages results.",
        epilog="""
Example:
  python3 bench_avg.py --runs 10 my_benchmark_filter

This will run `cargo bench` 10 times with the filter `my_benchmark_filter`, and print the averaged results.
"""
    )
    parser.add_argument('--runs', type=int, default=5, help='Number of times to run `cargo bench` (default: 5)')
    parser.add_argument('bench_args', nargs=argparse.REMAINDER)
    args = parser.parse_args()

    results = []

    for i in range(args.runs):
        print(f"Run {i+1}/{args.runs}...")
        proc = subprocess.run(['cargo', 'bench'] + args.bench_args,
                               capture_output=True, text=True)
        if proc.returncode != 0:
            print(proc.stderr, file=sys.stderr)
            sys.exit(proc.returncode)
        out = proc.stdout

        # with open('/tmp/outfile', 'r') as f:
        #     out = f.read()

        # print("Raw Benchmark Output:\n", out, "\n")
        data = parse_divan_output(out)
        # print("Parsed Benchmark Data:\n", data, "\n")
        results.extend(data)

    averaged = average_fields(results)
    out = render_divan_table(averaged)
    print(out)

if __name__ == '__main__':
    main()
