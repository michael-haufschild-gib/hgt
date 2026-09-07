"""All-state hostile extension of the frozen reserve induction, RunPod only."""
import csv
import hashlib
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
    primes = [p for p in range(2, cutoff) if all(p % d for d in range(2, math.isqrt(p)+1))]
    labels = {}
    channels = {}
    for d in range(1, cutoff):
        if any(d % (p*p) == 0 for p in primes):
            continue
        mask = sum(1 << i for i, p in enumerate(primes) if d % p == 0)
        q = cutoff // d
        value = np.sqrt(np.longdouble(d))*CLOCK[q] + (
            np.sqrt(np.longdouble(cutoff))-np.sqrt(np.longdouble(d*q)))*DEFECT[q]
        labels[mask] = value
        channels[d] = value
    size = 1 << len(primes)
    indices = np.arange(size, dtype=np.int64)
    good = np.zeros(size, dtype=np.longdouble)
    defect = np.zeros(size, dtype=np.longdouble)
    for label in labels:
        fibre = np.zeros(size, dtype=np.longdouble)
        for source, value in labels.items():
            if source & label == label:
                extra = source ^ label
                fibre[extra] = (-1 if bin(extra).count('1') % 2 else 1)*value
        for i in range(len(primes)):
            bit = 1 << i
            if label & bit:
                continue
            blocks = fibre.reshape(-1, 2, bit)
            blocks[:, 1, :] += blocks[:, 0, :]
        good += np.maximum(fibre, 0)**2
        defect += np.minimum(fibre, 0)**2
    energy = good + defect
    phi = energy + 2*np.sqrt(good*defect)
    initial = energy[0]
    tol = 1e-12*max(1, initial)
    assert abs(initial - SAVED[cutoff]) <= tol
    certified = phi <= initial + tol
    possible = np.zeros(size, dtype=bool)
    for i in range(len(primes)):
        bit = 1 << i
        lacking = indices[(indices & bit) == 0]
        successors = lacking | bit
        possible[lacking] |= certified[successors] | (successors == size-1)
    failing = indices[certified & ~possible & (indices != size-1)]

    def record(mask):
        return dict(M=cutoff, mask=int(mask), P=[p for i, p in enumerate(primes) if mask & (1 << i)],
                    energy=float(energy[mask]), good=float(good[mask]), defect=float(defect[mask]),
                    geometric_upper=float(phi[mask]), initial_energy=float(initial))

    max_audit_error = 0.0
    def direct_audit(mask):
        nonlocal max_audit_error
        state = dict(channels)
        for i, p in enumerate(primes):
            if mask & (1 << i):
                state = {d: value-state.get(p*d, 0) for d, value in state.items() if d % p}
        g = sum(max(v, 0)**2 for v in state.values())
        d = sum(min(v, 0)**2 for v in state.values())
        error = max(abs(g-good[mask]), abs(d-defect[mask]))
        max_audit_error = max(max_audit_error, float(error))
        assert error <= tol

    # All reported failures and their complete outgoing edge sets are audited.
    audited = set()
    failures = []
    for mask in failing:
        successors = [int(mask | (1 << i)) for i in range(len(primes)) if not mask & (1 << i)]
        for m in [int(mask)] + successors:
            if m not in audited:
                direct_audit(m)
                audited.add(m)
        failures.append(dict(state=record(mask), successors=[record(m) for m in successors]))
    # These deterministic boundary checks validate successful jobs too.
    for mask in [0, size-1] + [1 << i for i in range(len(primes))]:
        if mask not in audited:
            direct_audit(mask)
            audited.add(mask)
    return dict(M=cutoff, states=size, certified_proper=int(np.count_nonzero(certified[:-1])),
                extension_failure_count=len(failures), failures=failures,
                direct_audit_states=len(audited), max_direct_audit_error=max_audit_error,
                original_diagonal_error=float(abs(initial - SAVED[cutoff])))


if __name__ == '__main__':
    started = time.monotonic()
    source = Path('first-prime-unit-clock.csv')
    rows = list(csv.DictReader(source.open()))
    DEFECT = np.array([row['defect'] for row in rows], dtype=np.longdouble)
    CLOCK = np.array([row['unit_channel'] for row in rows], dtype=np.longdouble)
    saved = Path('greedy-summary.json')
    SAVED = {row['M']: row['initial'] for row in json.loads(saved.read_text())}
    workers = min(8, os.cpu_count() or 1)
    with mp.get_context('fork').Pool(workers) as pool:
        results = pool.map(inspect_cutoff, range(33, 65))
    failures = [f for r in results for f in r['failures']]
    result = dict(question='Local certificate extension, every subset at M=33..64',
                  input_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [source, saved]},
                  tolerance='1e-12*max(1,initial_energy)', workers=workers,
                  elapsed_seconds=time.monotonic()-started,
                  states=sum(r['states'] for r in results),
                  certified_proper=sum(r['certified_proper'] for r in results),
                  extension_failure_count=len(failures),
                  first_extension_failure=failures[0] if failures else None, results=results)
    Path('extension-summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'results'}, indent=2))
