#!/usr/bin/env python3
"""Summarize the frozen output on RunPod; no additional experiments."""
import json
from pathlib import Path

data = json.loads(Path('results.json').read_text())
print('| M | Source | A / D interval | A | B / D interval | B |')
print('|---:|:---|:---|:---|:---|:---|')
for c in data['results']:
    a, b = c['test_A'], c['test_B']
    print(f"| {c['M']} | {c['source']} | [{a['lower_over_D']:.6f}, {a['upper_over_D']:.6f}] | "
          f"{a['classification']} | [{b['lower_over_D']:.6f}, {b['upper_over_D']:.6f}] | {b['classification']} |")
print('\nMaximum validation discrepancies:')
for key in data['results'][0]['controls']:
    values = [c['controls'][key] for c in data['results'] if c['controls'][key] is not None]
    print(key, max(values))
print('\nComplete absolute budgets:')
for c in data['results']:
    print(c['M'], c['source'], {key: c[key] for key in (
        'diagonal', 'head_signed_sum', 'head_abs_sum', 'polynomial_abs_sum',
        'corrected_head_abs_sum', 'tail_abs_sum_lower', 'tail_abs_sum_upper')})
print('\nElapsed seconds:', data['elapsed_seconds'])
