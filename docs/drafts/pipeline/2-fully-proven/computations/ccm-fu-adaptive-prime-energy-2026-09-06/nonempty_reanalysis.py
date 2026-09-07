"""Frozen nonempty-energy diagnostic using stored full-energy edges only."""
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
limit = max(rows)
primes = [p for p in range(2, limit) if all(p % d for d in range(2, math.isqrt(p) + 1))]
# Same Euler constant and literal first-block coefficient as the original screen.
defect_one = 2 * 0.5772156649015328606065120900824 - 1
first = None
bad = edges = 0
max_anchor_spread = 0.0
minimum_nonempty_energy = 0.0
results = []
for cutoff, energy in rows.items():
    universe = [p for p in primes if p < cutoff]
    tolerance = 1e-12 * max(1, energy[0])
    late = [p for p in universe if 2 * p > cutoff]
    if not late:
        # Empty prime universe: only head energy, no edges to test.
        assert len(energy) == 1
        results.append({'M': cutoff, 'nonincreasing_path': [], 'edges': 0})
        continue
    heads = {}
    for mask, value in energy.items():
        anchors = []
        for prime in late:
            bit = 1 << universe.index(prime)
            coefficient = -(math.sqrt(cutoff) - math.sqrt(prime)) * defect_one
            if mask & bit:
                anchors.append((value - energy[mask ^ bit]) / (2 * coefficient) + coefficient)
            else:
                anchors.append((energy[mask | bit] - value) / (2 * coefficient))
        max_anchor_spread = max(max_anchor_spread, max(anchors) - min(anchors))
        heads[mask] = anchors[-1]
    tail = {mask: value - heads[mask] ** 2 for mask, value in energy.items()}
    minimum_nonempty_energy = min(minimum_nonempty_energy, min(tail.values()))
    paths = {0: []}
    local_edges = 0
    for mask in range(1, len(energy)):
        for i, prime in enumerate(universe):
            if not mask >> i & 1:
                continue
            previous = mask ^ (1 << i)
            delta = tail[mask] - tail[previous]
            edges += 1
            local_edges += 1
            if delta > tolerance:
                bad += 1
                if first is None:
                    first = {'M': cutoff, 'P': [p for j, p in enumerate(universe) if previous >> j & 1],
                             'prime': prime, 'before': tail[previous], 'after': tail[mask],
                             'head_before': heads[previous], 'head_after': heads[mask],
                             'initial_energy': energy[0]}
            elif previous in paths and mask not in paths:
                paths[mask] = paths[previous] + [prime]
    results.append({'M': cutoff, 'nonincreasing_path': paths.get(len(energy) - 1), 'edges': local_edges})
summary = {
    'question': 'Every nonempty-energy edge contracts; separately, existence of a complete contracting path.',
    'method': 'All stored subset states; heads recovered from isolated late-prime energy differences.',
    'tolerance': '1e-12*max(1,initial_energy)',
    'input_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'first_growing_edge': first,
    'edges': edges,
    'growing_edges': bad,
    'first_path_failure': next((row for row in results if row['nonincreasing_path'] is None), None),
    'max_head_disagreement_between_late_anchors': max_anchor_spread,
    'minimum_reconstructed_nonempty_energy': minimum_nonempty_energy,
    'results': results,
}
(BASE / 'nonempty-reanalysis.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({key: value for key, value in summary.items() if key != 'results'}, indent=2))
