"""Frozen final-overlap test of actual reserve extension. RunPod only."""
import csv
import hashlib
import itertools
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import time

os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import numpy as np


def inspect_cutoff(cutoff):
    small = [p for p in PRIMES if p*p < cutoff]
    size = 1 << len(small)
    labels = np.zeros(cutoff-1, dtype=np.int32)
    ds = np.arange(1, cutoff, dtype=np.int32)
    for i, p in enumerate(small):
        labels[ds % p == 0] |= 1 << i
    q = cutoff // ds
    unsigned = np.sqrt(ds)*CLOCK[q] + (math.sqrt(cutoff)-np.sqrt(ds*q))*DEFECT[q]
    source = MU[1:cutoff]*unsigned
    initial = float(np.sum(source**2))
    tol = 1e-12*max(1.0, initial)
    assert abs(initial-SAVED[cutoff]) <= tol
    parity = np.array([(-1 if bin(m).count('1') % 2 else 1) for m in range(size)])
    fields = {}
    for count in range(min(5, len(small))+1):
        for subset in itertools.combinations(range(len(small)), count):
            mask = sum(1 << i for i in subset)
            fibre = np.bincount(labels & mask, weights=source, minlength=size)
            oriented = parity*fibre
            good = float(np.sum(np.maximum(oriented, 0)**2))
            defect = float(np.sum(np.minimum(oriented, 0)**2))
            energy = good+defect
            fields[mask] = dict(energy=energy, good=good, defect=defect,
                                phi=energy+2*math.sqrt(good*defect))
    full_source = fields[0]['energy']
    certified_count = 0
    failures = []
    two_boundary_error = 0.0
    closest = None
    for mask, value in fields.items():
        count = bin(mask).count('1')
        if count < 2:
            continue
        successors = []
        for i, p in enumerate(small):
            if mask & (1 << i):
                nxt = fields[mask ^ (1 << i)]
                successors.append(dict(prime=p, **nxt))
                if count == 2:
                    # For a final oriented pair, Phi=max(its energy, final signed square).
                    two_boundary_error = max(two_boundary_error,
                        abs(nxt['phi']-max(nxt['energy'], full_source)))
        if value['phi'] > initial+tol:
            continue
        certified_count += 1
        best = min(successors, key=lambda s: (s['phi'], s['prime']))
        reserve = initial-best['phi']
        item = dict(M=cutoff, remaining=[p for i, p in enumerate(small) if mask & (1 << i)],
                    initial_energy=initial, terminal_energy=full_source, current=value,
                    successors=successors, best_successor_reserve=reserve)
        if closest is None or reserve/initial < closest['best_successor_reserve']/initial:
            closest = item
        if best['phi'] > initial+tol:
            # Independent complete-source accumulation, no bincount or parity-zeta reuse.
            groups = {}
            for d, coefficient in zip(ds.tolist(), source.tolist()):
                retained = math.prod(p for p in item['remaining'] if d % p == 0)
                groups.setdefault(retained, []).append(coefficient)
            checked = {r: math.fsum(terms) for r, terms in groups.items()}
            g = math.fsum(max(MU[r]*v, 0)**2 for r, v in checked.items())
            de = math.fsum(min(MU[r]*v, 0)**2 for r, v in checked.items())
            assert max(abs(g-value['good']), abs(de-value['defect'])) <= tol
            for nxt in successors:
                p = nxt['prime']
                merged = {r: v+checked.get(p*r, 0.0) for r, v in checked.items() if r % p}
                ng = math.fsum(max(MU[r]*v, 0)**2 for r, v in merged.items())
                nd = math.fsum(min(MU[r]*v, 0)**2 for r, v in merged.items())
                assert max(abs(ng-nxt['good']), abs(nd-nxt['defect'])) <= tol
            item['fibres'] = checked
            item['tolerance'] = tol
            failures.append(item)
    assert two_boundary_error <= tol
    return dict(M=cutoff, tested_states=sum(bin(m).count('1') >= 2 for m in fields),
                certified_states=certified_count, failures=failures, closest=closest,
                two_prime_boundary_error=two_boundary_error)


if __name__ == '__main__':
    start = time.monotonic()
    table = Path('first-prime-unit-clock.csv')
    saved = Path('greedy-summary.json')
    rows = list(csv.DictReader(table.open()))
    DEFECT = np.array([float(r['defect']) for r in rows])
    CLOCK = np.array([float(r['unit_channel']) for r in rows])
    SAVED = {r['M']: r['initial'] for r in json.loads(saved.read_text())}
    PRIMES = [p for p in range(2, 1025) if all(p % d for d in range(2, math.isqrt(p)+1))]
    MU = np.ones(1025, dtype=np.int32)
    MU[0] = 0
    for p in PRIMES:
        MU[p::p] *= -1
        MU[p*p::p*p] = 0
    workers = min(8, os.cpu_count() or 1)
    with mp.get_context('fork').Pool(workers) as pool:
        results = pool.map(inspect_cutoff, range(65, 1025))
    failures = [f for r in results for f in r['failures']]
    result = dict(question='All remaining-small-prime fields of size2..5 at every M65..1024',
                  input_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [table, saved]},
                  workers=workers, elapsed_seconds=time.monotonic()-start,
                  tested_states=sum(r['tested_states'] for r in results),
                  certified_states=sum(r['certified_states'] for r in results),
                  failure_count=len(failures), first_failure=failures[0] if failures else None,
                  results=results)
    Path('summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'results'}, indent=2))
