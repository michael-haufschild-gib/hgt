"""Frozen prescribed-prime repair diagnostic. Execute only on RunPod."""
import csv
import hashlib
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import signal
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
    error = max(abs(energies[m] - csv_energy[m]) for m in states)
    assert error <= tol

    def children(mask):
        return [(p, mask | (1 << i)) for i, p in enumerate(primes)
                if not mask & (1 << i)]

    witnesses = [max([m] + [n for _, n in children(m)], key=lambda n: energies[n])
                 for m in states]
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
    distance = [math.inf] * (full + 1)
    paths = [None] * (full + 1)
    for mask in range(full, -1, -1):
        if admitted[mask]:
            distance[mask], paths[mask] = 0, []
        elif energies[mask] <= budget + tol:
            options = [(distance[n] + 1, p, n) for p, n in children(mask)
                       if math.isfinite(distance[n])]
            if options:
                d, p, n = min(options)
                distance[mask], paths[mask] = d, [p] + paths[n]
    failures, counts, tested = [], {}, 0
    for mask in range(full):
        if not admitted[mask]:
            continue
        for r, child in children(mask):
            tested += 1
            delay = 1 + distance[child]
            key = 'infinite' if not math.isfinite(delay) else str(int(delay))
            counts[key] = counts.get(key, 0) + 1
            if delay <= 2:
                continue
            failures.append(dict(
                M=record['M'], mask=mask, P=states[mask]['P'], forced_prime=r,
                first_mask=child, budget=budget, envelope=envelope[mask],
                first_energy=energies[child], first_envelope=envelope[child],
                first_witness=witnesses[child], reachable_path=reachable.get(mask),
                min_mergers_to_admission=None if not math.isfinite(delay) else int(delay),
                shortest_repair=None if paths[child] is None else [r] + paths[child],
                alternatives=[dict(prime=q, mask=n, energy=energies[n],
                    envelope=envelope[n], witness_mask=witnesses[n]) for q, n in children(child)]))
    audit = direct_audit(record['M'], primes, energies, failures, children) if failures else None
    return dict(M=record['M'], states=len(states), tested=tested, admitted=sum(admitted),
                max_csv_error=error, repair_length_counts=counts, failures=failures,
                direct_audit=audit)


def direct_audit(cutoff, primes, stored, failures, children):
    import mpmath as m
    m.mp.dps = 80
    defect = [m.mpf(0)] + [m.fsum(m.log(j) for j in range(1, n + 1))
        - sum(n // d for d in range(1, n + 1)) + 2 * m.euler * n
        for n in range(1, cutoff)]
    coefficients = []
    for d in range(1, cutoff):
        if any(d % (p * p) == 0 for p in primes):
            continue
        support = sum(1 << i for i, p in enumerate(primes) if d % p == 0)
        mu = (-1) ** support.bit_count()
        value = mu * m.fsum((m.sqrt(k + 1) - m.sqrt(k)) * defect[k // d]
                            for k in range(d, cutoff))
        coefficients.append((support, value))
    budget = m.fsum(v * v for _, v in coefficients)
    tolerance = m.mpf('1e-12') * max(1, budget)
    cache = {}

    def field(mask):
        if mask not in cache:
            grouped = {}
            for support, value in coefficients:
                grouped.setdefault(support & ~mask, []).append(value)
            oriented = {r: (-1) ** r.bit_count() * m.fsum(vs) for r, vs in grouped.items()}
            energy = m.fsum(v * v for v in oriented.values())
            assert abs(energy - stored[mask]) <= tolerance
            cache[mask] = energy, oriented
        return cache[mask]

    def envelope(mask):
        return max(field(n)[0] for n in [mask] + [n for _, n in children(mask)])

    show = lambda x: m.nstr(x, 65)
    for failure in failures:
        parent, child = failure['mask'], failure['first_mask']
        assert envelope(parent) <= budget + tolerance
        assert field(child)[0] <= budget + tolerance
        assert envelope(child) > budget + tolerance
        gaps = {}
        for q, n in children(child):
            gap = envelope(n) - budget
            assert gap > tolerance
            gaps[str(q)] = show(gap)
        failure['direct_audit'] = dict(parent_margin=show(budget - envelope(parent)),
            first_envelope_excess=show(envelope(child) - budget),
            alternative_envelope_excess=gaps)
        if failure['shortest_repair']:
            mask = parent
            for p in failure['shortest_repair']:
                mask |= 1 << primes.index(p)
                assert field(mask)[0] <= budget + tolerance
            assert envelope(mask) <= budget + tolerance
    return dict(digits=80, budget=show(budget), reconstructed_states=len(cache),
        max_stored_error=show(max(abs(e - stored[n]) for n, (e, _) in cache.items())),
        fields={str(n): dict(energy=show(e), oriented={str(r): show(v) for r, v in vals.items()})
                for n, (e, vals) in sorted(cache.items())})


if __name__ == '__main__':
    signal.alarm(50)
    started = time.monotonic()
    source, source_csv = Path('defect-reserve-reanalysis.json'), Path('subset-states.csv')
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
    lengths = {}
    for record in results:
        for key, count in record['repair_length_counts'].items():
            lengths[key] = lengths.get(key, 0) + count
    summary = dict(question='Every admitted proper actual state repairs every prescribed first prime in at most two mergers under the original budget.',
        input_sha256={source.name: hashlib.sha256(raw).hexdigest(),
                      source_csv.name: hashlib.sha256(source_csv.read_bytes()).hexdigest()},
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        workers=workers, elapsed_seconds=time.monotonic() - started,
        states=sum(r['states'] for r in results), tested=sum(r['tested'] for r in results),
        failures=len(failures), reachable_failures=sum(f['reachable_path'] is not None for f in failures),
        repair_length_counts=lengths, first_failure=failures[0] if failures else None,
        results=results)
    Path('summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
    signal.alarm(0)
