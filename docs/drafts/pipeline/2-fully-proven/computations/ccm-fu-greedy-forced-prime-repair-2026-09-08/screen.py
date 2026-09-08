"""Frozen greedy repair diagnostic. Execute only on the supplied RunPod host."""
import csv
import hashlib
import json
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
    energies = [states[n]['energy'] for n in range(full + 1)]
    budget = states[0]['initial_energy']
    tol = 1e-12 * max(1.0, budget)
    assert set(csv_energy) == set(states)
    error = max(abs(energies[n] - csv_energy[n]) for n in states)
    assert error <= tol

    def children(mask):
        return [(p, mask | (1 << i)) for i, p in enumerate(primes)
                if not mask & (1 << i)]

    witnesses = [max([n] + [s for _, s in children(n)], key=lambda s: energies[s])
                 for n in states]
    envelope = [energies[w] for w in witnesses]
    admitted = [v <= budget + tol for v in envelope]
    boundary = {}
    for parent in range(full):
        if not admitted[parent]:
            continue
        for forced, child in children(parent):
            if not admitted[child]:
                boundary.setdefault(child, []).append(dict(mask=parent, forced_prime=forced))

    failures, cases = [], []
    for child, parents in sorted(boundary.items()):
        options = children(child)
        assert options
        q, chosen = min(options, key=lambda item: (energies[item[1]], item[0]))
        near = [(p, n) for p, n in options if energies[n] <= energies[chosen] + tol]
        failed_near = [(p, n) for p, n in near if not admitted[n]]
        case = dict(M=record['M'], mask=child, P=states[child]['P'], parents=parents,
            energy=energies[child], envelope=envelope[child], chosen_prime=q,
            chosen_mask=chosen, chosen_admitted=admitted[chosen],
            near_minimum=[p for p, _ in near], failed_near=[p for p, _ in failed_near],
            alternatives=[dict(prime=p, mask=n, energy=energies[n], envelope=envelope[n],
                witness_mask=witnesses[n], admitted=admitted[n]) for p, n in options])
        cases.append(case)
        if failed_near:
            interactions = []
            for p, n in failed_near:
                w = witnesses[n]
                extra = w ^ n
                if not extra:
                    interactions.append(dict(repair=p, current_energy_excess=energies[n] - budget))
                    continue
                assert extra & (extra - 1) == 0
                s = primes[extra.bit_length() - 1]
                for origin in parents:
                    base, r = origin['mask'], origin['forced_prime']
                    rb, pb, sb = (1 << primes.index(t) for t in (r, p, s))
                    first = [energies[base | b] - energies[base] for b in (rb, pb, sb)]
                    second = [energies[base | a | b] - energies[base | a]
                        - energies[base | b] + energies[base] for a, b in ((rb, pb), (rb, sb), (pb, sb))]
                    third = energies[w] - energies[base] - sum(first) - sum(second)
                    interactions.append(dict(parent=base, forced=r, repair=p, successor=s,
                        first=first, second=second, third=third,
                        parent_slack=budget - energies[base], final_excess=energies[w] - budget))
            case['failed_interactions'] = interactions
            failures.append(case)
    audit = direct_audit(record['M'], primes, energies, failures, children) if failures else None
    return dict(M=record['M'], states=len(states), max_csv_error=error,
        forced_boundary_transitions=sum(map(len, boundary.values())), boundary_states=len(boundary),
        failed_choices=sum(not c['chosen_admitted'] for c in cases),
        flagged_near_minimum_states=len(failures), cases=cases, direct_audit=audit)


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
        value = (-1) ** support.bit_count() * m.fsum(
            (m.sqrt(k + 1) - m.sqrt(k)) * defect[k // d] for k in range(d, cutoff))
        coefficients.append((support, value))
    budget = m.fsum(v * v for _, v in coefficients)
    tol = m.mpf('1e-12') * max(1, budget)
    cache = {}

    def field(mask):
        if mask not in cache:
            grouped = {}
            for support, value in coefficients:
                grouped.setdefault(support & ~mask, []).append(value)
            signed = {r: m.fsum(vs) for r, vs in grouped.items()}
            energy = m.fsum(v * v for v in signed.values())
            assert abs(energy - stored[mask]) <= tol
            cache[mask] = energy, signed
        return cache[mask]

    def envelope(mask):
        labels = [mask] + [n for _, n in children(mask)]
        witness = max(labels, key=lambda n: field(n)[0])
        return field(witness)[0], witness

    show = lambda x: m.nstr(x, 65)
    for failure in failures:
        child = failure['mask']
        assert field(child)[0] <= budget + tol
        assert envelope(child)[0] > budget + tol
        for parent in failure['parents']:
            assert envelope(parent['mask'])[0] <= budget + tol
        options = sorted(children(child), key=lambda pn: (field(pn[1])[0], pn[0]))
        q, best = options[0]
        gap = None if len(options) == 1 else field(options[1][1])[0] - field(best)[0]
        failure['direct_audit'] = dict(chosen_prime=q, chosen_mask=best,
            energy_gap_to_next=None if gap is None else show(gap),
            unresolved_minimum=gap is not None and gap <= m.mpf('1e-60'),
            chosen_envelope_excess=show(envelope(best)[0] - budget),
            chosen_failed=envelope(best)[0] > budget + tol,
            alternatives=[dict(prime=p, mask=n, energy=show(field(n)[0]),
                envelope_excess=show(envelope(n)[0] - budget), witness_mask=envelope(n)[1])
                for p, n in options])
    return dict(digits=80, budget=show(budget), reconstructed_states=len(cache),
        max_stored_error=show(max(abs(e - stored[n]) for n, (e, _) in cache.items())),
        fields={str(n): dict(energy=show(e), signed={str(r): show(v) for r, v in vals.items()})
                for n, (e, vals) in sorted(cache.items())})


def deadline(_signum, _frame):
    raise TimeoutError('Frozen 50-second computation deadline')


def initialize_worker():
    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    signal.signal(signal.SIGALRM, signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
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
    with mp.Pool(workers, initializer=initialize_worker) as pool:
        results = pool.map(inspect_cutoff, jobs)
    failures = [c for r in results for c in r['cases'] if c['failed_near']]
    summary = dict(question='Immediate-energy minimization repairs every forced transition out of exact successor admission.',
        input_sha256={source.name: hashlib.sha256(raw).hexdigest(),
                      source_csv.name: hashlib.sha256(source_csv.read_bytes()).hexdigest()},
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        workers=workers, elapsed_seconds=time.monotonic() - started,
        states=sum(r['states'] for r in results),
        forced_boundary_transitions=sum(r['forced_boundary_transitions'] for r in results),
        boundary_states=sum(r['boundary_states'] for r in results),
        failed_choices=sum(r['failed_choices'] for r in results),
        flagged_near_minimum_states=len(failures), first_flagged=failures[0] if failures else None,
        results=results)
    Path('summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
    signal.alarm(0)
