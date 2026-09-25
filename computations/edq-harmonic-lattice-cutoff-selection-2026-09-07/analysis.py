#!/usr/bin/env python3
"""Summarize the fixed experiment on RunPod, without changing its prediction."""
import json
from pathlib import Path

data = json.loads(Path('results.json').read_text())
print('| Band | S cutoff | G cutoff | S full energy | G full energy | Result |')
print('|:---|---:|---:|:---|:---|:---|')
for s in data['selections']:
    si, gi = s['scalar_complete_energy'], s['gcd_complete_energy']
    print(f"| {s['band']} | {s['scalar']['N']} | {s['gcd']['N']} | "
          f"[{si[0]:.9f}, {si[1]:.9f}] | [{gi[0]:.9f}, {gi[1]:.9f}] | {s['classification']} |")
print('\nHead and tail decomposition:')
for s in data['selections']:
    delta_head = s['gcd_head_energy']-s['scalar_head_energy']
    delta_tail = [s['gcd_later_tail'][0]-s['scalar_later_tail'][1],
                  s['gcd_later_tail'][1]-s['scalar_later_tail'][0]]
    print(s['band'], 'G-S head:', delta_head, 'G-S tail interval:', delta_tail)
print('\nValidation and resources:')
print('scan reconstruction maximum:', data['scan_max_reconstruction_error'])
print('selected-source direct residue maximum:', max(c['accumulation_max_error'] for c in data['results']))
print('closed-head identity maximum:', max(c['head_closed_form_error'] for c in data['results']))
print('analytic tail maximum:', max(c['analytic_tail_bound'] for c in data['results']))
print('maximum prefix terminal:', max(c['prefix_terminal'] for c in data['results']))
print('total prefix lengths:', sum(c['prefix_terminal'] for c in data['results']))
for kind in ('scalar', 'gcd'):
    print(kind, 'minimum runner-up gap:', min(s[kind+'_runner_up_gap'] for s in data['selections']))
print('wall seconds:', data['elapsed_seconds'])
