"""Frozen overlap-phase diagnostic; reads stored energies only. Never a Lean input."""
import collections
import csv
import hashlib
import json
import math
from pathlib import Path

BASE = Path(__file__).resolve().parent
states = collections.defaultdict(dict)
with (BASE / 'subset-states.csv').open() as handle:
    for row in csv.DictReader(handle):
        states[int(row['M'])][int(row['mask'])] = float(row['energy'])
with (BASE / 'greedy-stages.csv').open() as handle:
    stages = list(csv.DictReader(handle))
limit = max(int(row['M']) for row in stages)
primes = [p for p in range(2, limit) if all(p % d for d in range(2, math.isqrt(p) + 1))]

def overlap_pair(cutoff, remaining):
    if len(remaining) > 1 and remaining[0] * remaining[1] < cutoff:
        return remaining[:2]
    return None

traps = []
examined = 0
for cutoff, energies in states.items():
    universe = [p for p in primes if p < cutoff]
    tolerance = 1e-12 * max(1, energies[0])
    for mask, energy in energies.items():
        remaining = [p for i, p in enumerate(universe) if not (mask >> i & 1)]
        pair = overlap_pair(cutoff, remaining)
        if pair is None:
            continue
        examined += 1
        choices = [(energies[mask | (1 << i)] - energy, p)
                   for i, p in enumerate(universe) if not (mask >> i & 1)]
        if min(choices)[0] > tolerance:
            traps.append({'M': cutoff, 'mask': mask,
                          'P': [p for i, p in enumerate(universe) if mask >> i & 1],
                          'overlap_pair': pair, 'energy': energy,
                          'initial': energies[0], 'best_increase': min(choices)})

greedy_traps = []
active = 0
old_cutoff = None
for row in stages:
    cutoff = int(row['M'])
    if cutoff != old_cutoff:
        remaining = [p for p in primes if p < cutoff]
        old_cutoff = cutoff
    pair = overlap_pair(cutoff, remaining)
    if pair is not None:
        active += 1
        tolerance = 1e-12 * max(1, float(row['initial_energy']))
        if float(row['next_energy']) > float(row['previous_energy']) + tolerance:
            greedy_traps.append(dict(row, overlap_pair=pair, remaining=remaining.copy()))
    remaining.remove(int(row['prime']))

result = {
    'scope': 'Every saved subset state and greedy stage; no channels or paths regenerated.',
    'tolerance': '1e-12*max(1,initial_energy)',
    'input_sha256': {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                     for name in ['subset-states.csv', 'greedy-stages.csv']},
    'overlap_states': examined,
    'forced_increase_states': len(traps),
    'first_forced_increase_states': traps[:4],
    'greedy_overlap_stages': active,
    'greedy_overlap_increases': len(greedy_traps),
    'first_greedy_overlap_increases': greedy_traps[:3],
}
(BASE / 'overlap-reanalysis.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({key: value for key, value in result.items()
                  if key in ['overlap_states', 'forced_increase_states',
                             'greedy_overlap_stages', 'greedy_overlap_increases']}, indent=2))
