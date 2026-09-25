"""Frozen exact-successor extension diagnostic. Execute only on RunPod."""
import csv
import hashlib
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import time


def inspect_cutoff(job):
    record, csv_energy = job
    states = {s['mask']: s for s in record['states']}
    full = max(states)
    assert set(states) == set(range(full + 1))
    primes = states[full]['P']
    assert full == (1 << len(primes)) - 1
    budget = states[0]['initial_energy']
    tol = 1e-12 * max(1.0, budget)
    energies = [states[m]['energy'] for m in range(full + 1)]
    assert set(csv_energy) == set(states)
    max_error = max(abs(energies[m] - csv_energy[m]) for m in states)
    assert max_error <= tol

    def children(mask):
        return [(p, mask | (1 << i)) for i, p in enumerate(primes)
                if not mask & (1 << i)]

    witnesses = [max([m] + [n for _, n in children(m)],
                     key=lambda n: energies[n]) for m in states]
    envelope = [energies[n] for n in witnesses]
    admitted = [v <= budget + tol for v in envelope]
    reachable = {0: []} if admitted[0] else {}
    for mask in range(1, full + 1):
        if not admitted[mask]:
            continue
        for i, p in enumerate(primes):
            pred = mask ^ (1 << i)
            if mask & (1 << i) and pred in reachable:
                reachable[mask] = reachable[pred] + [p]
                break
    failures = []
    tested = 0
    for mask in range(full):
        if not admitted[mask]:
            continue
        tested += 1
        outgoing = children(mask)
        if any(admitted[n] for _, n in outgoing):
            continue
        failures.append(dict(
            M=record['M'], mask=mask, P=states[mask]['P'],
            energy=energies[mask], envelope=envelope[mask], budget=budget,
            reachable_path=reachable.get(mask),
            successors=[dict(prime=p, mask=n, energy=energies[n],
                             envelope=envelope[n], witness_mask=witnesses[n])
                        for p, n in outgoing]))
    if failures:
        audit_failures(record['M'], primes, energies, failures)
    return dict(M=record['M'], states=len(states), tested=tested,
                admitted=sum(admitted),
                additional_over_geometric=sum(admitted[m] and
                    states[m]['geometric_upper'] > budget + tol for m in states),
                reachable=len(reachable), full_path=reachable.get(full),
                max_csv_energy_error=max_error, failures=failures)


def audit_failures(cutoff, primes, stored, failures):
    import mpmath as mpf
    mpf.mp.dps = 80
    defect = [mpf.mpf(0)] + [
        mpf.fsum(mpf.log(j) for j in range(1, n + 1))
        - sum(n // d for d in range(1, n + 1)) + 2 * mpf.euler * n
        for n in range(1, cutoff)]
    coefficients = []
    for d in range(1, cutoff):
        if any(d % (p * p) == 0 for p in primes):
            continue
        support = sum(1 << i for i, p in enumerate(primes) if d % p == 0)
        mu = (-1) ** bin(support).count('1')
        value = mu * mpf.fsum((mpf.sqrt(k + 1) - mpf.sqrt(k)) * defect[k // d]
                             for k in range(d, cutoff))
        coefficients.append((support, value))
    budget = mpf.fsum(v * v for _, v in coefficients)
    tolerance = mpf.mpf('1e-12') * max(1, budget)
    cache = {}

    def children(mask):
        return [mask | (1 << i) for i in range(len(primes)) if not mask & (1 << i)]

    def field(mask):
        if mask not in cache:
            grouped = {}
            for support, value in coefficients:
                grouped.setdefault(support & ~mask, []).append(value)
            oriented = {r: (-1) ** bin(r).count('1') * mpf.fsum(vs)
                        for r, vs in grouped.items()}
            energy = mpf.fsum(v * v for v in oriented.values())
            assert abs(energy - stored[mask]) <= tolerance
            cache[mask] = energy, oriented
        return cache[mask]

    def envelope(mask):
        return max(field(n)[0] for n in [mask] + children(mask))

    def show(x):
        return mpf.nstr(x, 65)

    for failure in failures:
        mask = failure['mask']
        margin = budget - envelope(mask)
        assert margin >= -tolerance
        successor_margins = {n: budget - envelope(n) for n in children(mask)}
        assert all(v < -tolerance for v in successor_margins.values())
        needed = {mask}
        needed.update(children(mask))
        for n in children(mask):
            needed.update(children(n))
        failure['direct_audit'] = dict(
            digits=80, budget=show(budget), envelope_margin=show(margin),
            successor_envelope_margins={str(n): show(v) for n, v in successor_margins.items()},
            max_stored_error=show(max(abs(field(n)[0] - stored[n]) for n in needed)),
            fields={str(n): dict(energy=show(field(n)[0]),
                    oriented={str(r): show(v) for r, v in field(n)[1].items()})
                    for n in sorted(needed)})


if __name__ == '__main__':
    started = time.monotonic()
    source = Path('defect-reserve-reanalysis.json')
    source_csv = Path('subset-states.csv')
    raw = source.read_bytes()
    data = json.loads(raw)
    csv_energy = {}
    with source_csv.open() as handle:
        for row in csv.DictReader(handle):
            cutoff, mask = int(row['M']), int(row['mask'])
            assert mask not in csv_energy.setdefault(cutoff, {})
            csv_energy[cutoff][mask] = float(row['energy'])
    assert set(csv_energy) == {r['M'] for r in data['results']}
    jobs = [(r, csv_energy[r['M']]) for r in data['results']]
    workers = min(8, os.cpu_count() or 1, len(jobs))
    with mp.Pool(workers) as pool:
        results = pool.map(inspect_cutoff, jobs)
    failures = [f for r in results for f in r['failures']]
    summary = dict(
        question='Every proper actual state with current and all immediate successor energies below the original diagonal has a successor with the same property.',
        input_sha256={source.name: hashlib.sha256(raw).hexdigest(),
                      source_csv.name: hashlib.sha256(source_csv.read_bytes()).hexdigest()},
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        workers=workers, elapsed_seconds=time.monotonic() - started,
        states=sum(r['states'] for r in results), tested=sum(r['tested'] for r in results),
        additional_over_geometric=sum(r['additional_over_geometric'] for r in results),
        failures=len(failures), reachable_failures=sum(f['reachable_path'] is not None for f in failures),
        first_failure=failures[0] if failures else None,
        cutoffs_without_complete_path=[r['M'] for r in results if r['full_path'] is None],
        results=results)
    Path('summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
