"""Frozen one-step envelope-average test. Execute only on supplied RunPod."""
import csv
import hashlib
import json
import multiprocessing as pool_api
import os
from pathlib import Path
import time


def inspect(job):
    record, csv_energy = job
    states = {s['mask']: s for s in record['states']}
    full = max(states)
    primes = states[full]['P']
    assert set(states) == set(range(full + 1)) == set(csv_energy)
    assert full == (1 << len(primes)) - 1
    energy = [states[m]['energy'] for m in range(full + 1)]
    budget = states[0]['initial_energy']
    tolerance = 1e-12 * max(1.0, budget)
    error = max(abs(energy[m] - csv_energy[m]) for m in states)
    assert error <= tolerance

    def children(mask):
        return [(p, mask | (1 << i)) for i, p in enumerate(primes)
                if not mask & (1 << i)]

    envelope = [max([energy[m]] + [energy[n] for _, n in children(m)])
                for m in states]
    greedy = {0}
    current = 0
    while current != full:
        _, current = min(children(current), key=lambda pn: (energy[pn[1]], pn[0]))
        greedy.add(current)
    eligible = [m for m in range(full) if envelope[m] <= budget + tolerance]
    flagged = [m for m in eligible if
               sum(envelope[n] for _, n in children(m)) / len(children(m))
               > budget + tolerance]
    failures, fields, resolved = [], {}, []
    if flagged:
        import mpmath as mp
        mp.mp.dps = 80
        M = record['M']
        defects = [mp.mpf(0)] + [
            mp.fsum(mp.log(j) for j in range(1, k + 1))
            - sum(k // d for d in range(1, k + 1)) + 2 * mp.euler * k
            for k in range(1, M)]
        coefficients = []
        for d in range(1, M):
            if any(d % (p * p) == 0 for p in primes):
                continue
            support = sum(1 << i for i, p in enumerate(primes) if d % p == 0)
            value = (-1) ** bin(support).count('1') * mp.fsum(
                (mp.sqrt(k + 1) - mp.sqrt(k)) * defects[k // d] for k in range(d, M))
            coefficients.append((support, value))
        exact_budget = mp.fsum(value ** 2 for _, value in coefficients)
        exact_tolerance = mp.mpf('1e-12') * max(1, exact_budget)
        cache = {}

        def field(mask):
            if mask not in cache:
                grouped = {}
                for support, value in coefficients:
                    grouped.setdefault(support & ~mask, []).append(value)
                signed = {r: mp.fsum(values) for r, values in grouped.items()}
                actual = mp.fsum(value ** 2 for value in signed.values())
                assert abs(actual - energy[mask]) <= exact_tolerance
                cache[mask] = actual, signed
            return cache[mask]

        def psi(mask):
            return max([(field(mask)[0], None, mask)] + [
                (field(n)[0], p, n) for p, n in children(mask)], key=lambda x: x[0])

        def show(value):
            return mp.nstr(value, 65)

        for mask in flagged:
            current_psi = psi(mask)[0]
            assert current_psi <= exact_budget + exact_tolerance
            alternatives = []
            values = []
            for p, nxt in children(mask):
                value, q, witness = psi(nxt)
                values.append(value)
                alternatives.append(dict(prime=p, mask=nxt,
                    energy=show(field(nxt)[0]), envelope=show(value),
                    worst_second_prime=q, witness_mask=witness,
                    margin=show(exact_budget-value),
                    first_gain=show(field(nxt)[0]-field(mask)[0])))
            average = mp.fsum(values) / len(values)
            if average <= exact_budget + exact_tolerance:
                resolved.append(mask)
                continue
            p, nxt = min(children(mask), key=lambda pn: (field(pn[1])[0], pn[0]))
            failures.append(dict(M=M, mask=mask,
                P=[p for i, p in enumerate(primes) if mask & (1 << i)],
                budget=show(exact_budget), current_energy=show(field(mask)[0]),
                current_envelope=show(current_psi), average=show(average),
                excess=show(average-exact_budget),
                relative_excess=show((average-exact_budget)/exact_budget),
                on_stored_greedy_path=mask in greedy,
                least_energy_prime=p, least_energy_envelope=show(psi(nxt)[0]),
                alternatives=alternatives, digits=80))
        fields = {str(m): dict(energy=show(value),
                  signed={str(r): show(x) for r, x in signed.items()})
                  for m, (value, signed) in sorted(cache.items())}
    return dict(M=record['M'], states=len(states), tested=len(eligible),
                flagged=len(flagged), failures=failures,
                resolved=resolved, fields=fields, max_csv_error=error)


if __name__ == '__main__':
    started = time.monotonic()
    source = Path('defect-reserve-reanalysis.json')
    csv_source = Path('subset-states.csv')
    raw = source.read_bytes()
    data = json.loads(raw)
    csv_energy = {}
    with csv_source.open() as handle:
        for row in csv.DictReader(handle):
            cutoff, mask = int(row['M']), int(row['mask'])
            assert mask not in csv_energy.setdefault(cutoff, {})
            csv_energy[cutoff][mask] = float(row['energy'])
    assert set(csv_energy) == {r['M'] for r in data['results']}
    jobs = [(r, csv_energy[r['M']]) for r in data['results']]
    workers = min(8, os.cpu_count() or 1, len(jobs))
    with pool_api.Pool(workers) as pool:
        results = pool.map(inspect, jobs)
    failures = [f for r in results for f in r['failures']]
    summary = dict(question='Uniform mean of successor envelopes is at most the original diagonal at every proper admitted actual state.',
        input_sha256={source.name: hashlib.sha256(raw).hexdigest(),
                      csv_source.name: hashlib.sha256(csv_source.read_bytes()).hexdigest()},
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        workers=workers, elapsed_seconds=time.monotonic()-started,
        states=sum(r['states'] for r in results), tested=sum(r['tested'] for r in results),
        flagged=sum(r['flagged'] for r in results), failures=len(failures),
        resolved=sum(len(r['resolved']) for r in results),
        failures_on_stored_greedy_path=sum(f['on_stored_greedy_path'] for f in failures),
        first_failure=failures[0] if failures else None,
        results=results)
    Path('summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
