"""Frozen initial-subset ceiling diagnostic; stored energies only."""
import csv
import hashlib
import json
import math
from collections import defaultdict
from pathlib import Path

BASE = Path(__file__).resolve().parent
source = BASE / 'subset-states.csv'
rows = defaultdict(dict)
with source.open() as handle:
    for row in csv.DictReader(handle):
        rows[int(row['M'])][int(row['mask'])] = float(row['energy'])
by_cardinality = defaultdict(lambda: {'states': 0, 'failures': 0, 'first': None, 'max_ratio': 0})
first = None
for cutoff, energy in sorted(rows.items()):
    primes = [p for p in range(2, cutoff) if all(p % d for d in range(2, math.isqrt(p) + 1))]
    for mask, value in energy.items():
        size = bin(mask).count('1')
        entry = by_cardinality[size]
        entry['states'] += 1
        if energy[0] > 0:
            entry['max_ratio'] = max(entry['max_ratio'], value / energy[0])
        if value > energy[0] + 1e-12 * max(1, energy[0]):
            entry['failures'] += 1
            witness = {'M': cutoff, 'P': [p for i, p in enumerate(primes) if mask >> i & 1],
                       'energy': value, 'initial_energy': energy[0]}
            if entry['first'] is None:
                entry['first'] = witness
            if first is None:
                first = witness
summary = {
    'question': 'Do all initial subsets of at most two primes obey the original diagonal ceiling?',
    'method': 'All stored subset energies, grouped by processed cardinality; no channel regeneration.',
    'tolerance': '1e-12*max(1,initial_energy)',
    'input_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'first_failure': first,
    'by_cardinality': dict(sorted(by_cardinality.items())),
}
(BASE / 'cardinality-reanalysis.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
