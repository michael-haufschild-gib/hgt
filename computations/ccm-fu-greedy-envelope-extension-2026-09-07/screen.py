"""Frozen least-energy exact-envelope extension test. Run only on RunPod."""
import csv
import hashlib
import json
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
        if admitted[mask]:
            for i, p in enumerate(primes):
                pred = mask ^ (1 << i)
                if mask & (1 << i) and pred in reachable:
                    reachable[mask] = reachable[pred] + [p]
                    break
    greedy_masks = [0]
    while greedy_masks[-1] != full:
        _, n = min(children(greedy_masks[-1]), key=lambda pn: (energies[pn[1]], pn[0]))
        greedy_masks.append(n)

    tested = 0
    flagged = []
    for mask in range(full):
        if not admitted[mask]:
            continue
        tested += 1
        outgoing = children(mask)
        minimum = min(energies[n] for _, n in outgoing)
        near = [(p, n) for p, n in outgoing if energies[n] <= minimum + tol]
        if any(not admitted[n] for _, n in near):
            flagged.append(mask)

    failures, resolved = [], []
    if flagged:
        failures, resolved = audit_flags(record['M'], primes, energies, flagged,
                                         children, reachable, set(greedy_masks))
    return dict(M=record['M'], states=len(states), tested=tested,
                admitted=sum(admitted), flagged=len(flagged), resolved_near_ties=resolved,
                max_csv_energy_error=max_error, failures=failures,
                greedy_path_masks=greedy_masks,
                greedy_path_admitted=all(admitted[m] for m in greedy_masks))


def audit_flags(cutoff, primes, stored, flagged, children, reachable, greedy_masks):
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
        mu = (-1) ** support.bit_count()
        value = mu * mpf.fsum((mpf.sqrt(k + 1) - mpf.sqrt(k)) * defect[k // d]
                             for k in range(d, cutoff))
        coefficients.append((support, value))
    budget = mpf.fsum(v * v for _, v in coefficients)
    tolerance = mpf.mpf('1e-12') * max(1, budget)
    cache = {}

    def field(mask):
        if mask not in cache:
            grouped = {}
            for support, value in coefficients:
                grouped.setdefault(support & ~mask, []).append(value)
            oriented = {r: (-1) ** r.bit_count() * mpf.fsum(vs)
                        for r, vs in grouped.items()}
            energy = mpf.fsum(v * v for v in oriented.values())
            assert abs(energy - stored[mask]) <= tolerance
            cache[mask] = energy, oriented
        return cache[mask]

    def envelope(mask):
        return max([(field(mask)[0], None, mask)] +
                   [(field(n)[0], p, n) for p, n in children(mask)], key=lambda t: t[0])

    def show(x):
        return mpf.nstr(x, 65)

    failures, resolved = [], []
    for mask in flagged:
        outgoing = children(mask)
        p, nxt = min(outgoing, key=lambda pn: (field(pn[1])[0], pn[0]))
        current_envelope = envelope(mask)[0]
        assert current_envelope <= budget + tolerance
        if envelope(nxt)[0] <= budget + tolerance:
            resolved.append(dict(mask=mask, prime=p, margin=show(budget-envelope(nxt)[0])))
            continue
        needed = {mask}
        needed.update(n for _, n in outgoing)
        for _, n in outgoing:
            needed.update(nn for _, nn in children(n))
        alternatives = []
        for q, n in outgoing:
            value, worst_prime, worst_mask = envelope(n)
            details = dict(prime=q, mask=n, energy=show(field(n)[0]),
                           first_gain=show(field(n)[0]-field(mask)[0]),
                           envelope=show(value), margin=show(budget-value),
                           worst_second_prime=worst_prime, worst_mask=worst_mask,
                           admitted=bool(value <= budget+tolerance))
            if q != p:
                pair = nxt | n
                details['mixed_with_selected'] = show(
                    field(pair)[0]-field(nxt)[0]-field(n)[0]+field(mask)[0])
                details['selected_pair_margin'] = show(budget-field(pair)[0])
            alternatives.append(details)
        failures.append(dict(M=cutoff, mask=mask,
            P=[p for i, p in enumerate(primes) if mask & (1 << i)],
            selected_prime=p, selected_mask=nxt, budget=show(budget),
            current_energy=show(field(mask)[0]), current_envelope=show(current_envelope),
            current_margin=show(budget-current_envelope), digits=80,
            reachable_path=reachable.get(mask), on_empty_greedy_path=mask in greedy_masks,
            alternatives=alternatives,
            max_stored_error=show(max(abs(field(n)[0]-stored[n]) for n in needed)),
            fields={str(n): dict(energy=show(field(n)[0]),
                    oriented={str(r): show(v) for r, v in field(n)[1].items()})
                    for n in sorted(needed)}))
    return failures, resolved


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
        question='Least-energy successor, with smaller-prime tie break, preserves the exact one-successor envelope at every admitted proper actual state.',
        input_sha256={source.name: hashlib.sha256(raw).hexdigest(),
                      source_csv.name: hashlib.sha256(source_csv.read_bytes()).hexdigest()},
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        workers=workers, elapsed_seconds=time.monotonic()-started,
        states=sum(r['states'] for r in results), tested=sum(r['tested'] for r in results),
        flagged=sum(r['flagged'] for r in results), failures=len(failures),
        resolved_near_ties=sum(len(r['resolved_near_ties']) for r in results),
        reachable_failures=sum(f['reachable_path'] is not None for f in failures),
        failures_on_empty_greedy_path=sum(f['on_empty_greedy_path'] for f in failures),
        first_failure={k:v for k,v in failures[0].items() if k != 'fields'} if failures else None,
        results=results)
    Path('summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k != 'results'}, indent=2))
