"""Frozen PE4C diagnostic on stored energies; never a Lean premise."""
import csv
import hashlib
import json
import math
from collections import defaultdict
from pathlib import Path

BASE = Path(__file__).resolve().parent
source = BASE / "subset-states.csv"
states = defaultdict(dict)
with source.open() as handle:
    for row in csv.DictReader(handle):
        states[int(row["M"])][int(row["mask"])] = float(row["energy"])
limit = max(states)
primes = [p for p in range(2, limit) if all(p % d for d in range(2, math.isqrt(p) + 1))]
results = []
for bound in range(1, limit + 1):
    universe = [p for p in primes if p < bound]
    size = 1 << len(universe)
    safe = [True] * size
    for mask in range(size):
        for cutoff, energy in states.items():
            if cutoff > bound:
                continue
            restricted = mask & ((1 << sum(p < cutoff for p in universe)) - 1)
            if energy[restricted] > energy[0] + 1e-12 * max(1, energy[0]):
                safe[mask] = False
                break
    paths = {0: []}
    for mask in range(1, size):
        if safe[mask]:
            for i, prime in enumerate(universe):
                predecessor = mask ^ (1 << i)
                if mask >> i & 1 and predecessor in paths:
                    paths[mask] = paths[predecessor] + [prime]
                    break
    results.append({"bound": bound, "states": size, "safe_states": sum(safe),
                    "reachable_states": len(paths), "common_order": paths.get(size - 1)})
summary = {
    "question": "One prime order whose every prefix respects every cutoff at most the bound.",
    "tolerance": "1e-12*max(1,initial_energy)",
    "input_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "first_failure": next((row for row in results if row["common_order"] is None), None),
    "results": results,
}
(BASE / "common-order-reanalysis.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps({"first_failure": summary["first_failure"], "last_bound": results[-1]}, indent=2))
