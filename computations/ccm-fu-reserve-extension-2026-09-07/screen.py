"""Frozen local reserve-extension test; run only on RunPod, from saved states."""
import hashlib
import json
import multiprocessing as mp
import os
from pathlib import Path
import time


def inspect_cutoff(record):
    cutoff = record['M']
    states = {s['mask']: s for s in record['states']}
    full = max(states)
    primes = states[full]['P']
    initial = states[0]['initial_energy']
    tol = 1e-12 * max(1.0, initial)
    certified = {m: s['geometric_upper'] <= initial + tol for m, s in states.items()}
    reachable = {0: []}
    for mask in range(1, full + 1):
        for i, prime in enumerate(primes):
            bit = 1 << i
            predecessor = mask ^ bit
            if mask & bit and predecessor in reachable and certified[predecessor]:
                reachable[mask] = reachable[predecessor] + [prime]
                break
    extension_failures = []
    descent_failures = []
    certified_proper = 0
    for mask, state in states.items():
        if mask == full:
            continue
        successors = []
        for i, prime in enumerate(primes):
            next_mask = mask | (1 << i)
            if next_mask == mask:
                continue
            nxt = states[next_mask]
            successors.append(dict(prime=prime, **nxt))
        best = min(successors, key=lambda s: (s['geometric_upper'], s['prime']))
        if best['geometric_upper'] > state['geometric_upper'] + tol:
            descent_failures.append(dict(state=state, best_successor=best))
        if not certified[mask]:
            continue
        certified_proper += 1
        if all(s['mask'] != full and not certified[s['mask']] for s in successors):
            extension_failures.append(dict(
                state=state, successors=successors,
                certified_predecessor_path=reachable.get(mask),
                minimum_excess=best['geometric_upper'] - initial,
                tolerance=tol))
    return dict(M=cutoff, states=len(states), certified_proper=certified_proper,
                extension_failures=extension_failures,
                descent_failures=descent_failures)


if __name__ == '__main__':
    started = time.monotonic()
    source = Path('defect-reserve-reanalysis.json')
    data = json.loads(source.read_text())
    workers = min(8, os.cpu_count() or 1, len(data['results']))
    with mp.Pool(workers) as pool:
        results = pool.map(inspect_cutoff, data['results'])
    failures = [f for r in results for f in r['extension_failures']]
    descent = [f for r in results for f in r['descent_failures']]
    output = dict(
        question='Every certified proper actual state has a certified successor or completes.',
        input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        tolerance=data['tolerance'], workers=workers,
        elapsed_seconds=time.monotonic()-started,
        state_count=sum(r['states'] for r in results),
        certified_proper_count=sum(r['certified_proper'] for r in results),
        extension_failure_count=len(failures),
        reachable_extension_failure_count=sum(f['certified_predecessor_path'] is not None for f in failures),
        first_extension_failure=failures[0] if failures else None,
        homogeneous_descent_failure_count=len(descent),
        first_homogeneous_descent_failure=descent[0] if descent else None,
        results=results)
    Path('summary.json').write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'results'}, indent=2))
