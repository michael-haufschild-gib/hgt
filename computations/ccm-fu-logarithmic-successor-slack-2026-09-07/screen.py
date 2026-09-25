"""Frozen CCM-FU successor-slack diagnostic. Execute only on RunPod."""
import hashlib
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import time


def inspect_cutoff(record):
    states = {s['mask']: s for s in record['states']}
    full = max(states)
    primes = states[full]['P']
    budget = states[0]['initial_energy']
    tol = 1e-12 * max(1.0, budget)
    slack_tol = 1e-12 * max(1.0, budget**2)
    certified = {m: s['geometric_upper'] <= budget + tol for m, s in states.items()}
    reachable = {0: []}
    for mask in range(1, full + 1):
        for i, p in enumerate(primes):
            if mask & (1 << i):
                pred = mask ^ (1 << i)
                if pred in reachable and certified[pred]:
                    reachable[mask] = reachable[pred] + [p]
                    break
    failures, tested, worst = [], 0, None
    for mask, state in states.items():
        unused = [(i, p) for i, p in enumerate(primes) if not mask & (1 << i)]
        if not certified[mask] or len(unused) < 3:
            continue
        tested += 1
        outgoing = []
        for i, p in unused:
            nxt = states[mask | (1 << i)]
            slack = (budget - nxt['energy'])**2 - 4*nxt['good']*nxt['defect']
            outgoing.append(dict(prime=p, slack=slack, **nxt))
        mean = math.fsum(math.log(s['prime'])*s['slack'] for s in outgoing)
        mean /= math.fsum(math.log(s['prime']) for s in outgoing)
        result = dict(M=record['M'], state=state, mean_slack=mean,
                      normalized_mean_slack=mean/budget**2,
                      successors=outgoing, slack_tolerance=slack_tol,
                      certified_predecessor_path=reachable.get(mask))
        if worst is None or result['normalized_mean_slack'] < worst['normalized_mean_slack']:
            worst = result
        if mean < -slack_tol:
            failures.append(result)
    if failures:
        audit_failures(record['M'], primes, failures)
    return dict(M=record['M'], tested=tested, worst=worst, failures=failures)


def audit_failures(cutoff, primes, failures):
    """Reconstruct every failed field and successor independently from definitions."""
    import mpmath as m
    m.mp.dps = 80
    defect = [m.mpf(0)] + [
        m.fsum(m.log(j) for j in range(1, n+1))
        - sum(n//d for d in range(1, n+1)) + 2*m.euler*n
        for n in range(1, cutoff)]
    coefficients = []
    for d in range(1, cutoff):
        if any(d % (p*p) == 0 for p in primes):
            continue
        support = sum(1 << i for i, p in enumerate(primes) if d % p == 0)
        mu = (-1)**bin(support).count('1')
        value = mu*m.fsum((m.sqrt(k+1)-m.sqrt(k))*defect[k//d]
                         for k in range(d, cutoff))
        coefficients.append((support, value))
    budget = m.fsum(v*v for _, v in coefficients)
    cache = {}

    def field(mask):
        if mask in cache:
            return cache[mask]
        grouped = {}
        for support, value in coefficients:
            label = support & ~mask
            grouped.setdefault(label, []).append(value)
        oriented = {r: (-1)**bin(r).count('1')*m.fsum(vs) for r, vs in grouped.items()}
        good = m.fsum(v*v for v in oriented.values() if v >= 0)
        bad = m.fsum(v*v for v in oriented.values() if v < 0)
        result = (good+bad, good, bad, oriented)
        cache[mask] = result
        return result

    def show(x):
        return m.nstr(x, 65)

    for failure in failures:
        state = failure['state']
        energy, good, bad, oriented = field(state['mask'])
        outgoing = []
        max_error = max(abs(energy-state['energy']), abs(good-state['good']),
                        abs(bad-state['defect']), abs(budget-state['initial_energy']))
        weighted = m.mpf(0)
        total_weight = m.mpf(0)
        for s in failure['successors']:
            q, g, d, a = field(s['mask'])
            slack = (budget-q)**2-4*g*d
            weighted += m.log(s['prime'])*slack
            total_weight += m.log(s['prime'])
            max_error = max(max_error, abs(q-s['energy']), abs(g-s['good']), abs(d-s['defect']))
            outgoing.append(dict(prime=s['prime'], energy=show(q), good=show(g),
                                 defect=show(d), slack=show(slack),
                                 oriented={str(r): show(v) for r, v in a.items()}))
        mean = weighted/total_weight
        margin = budget-energy-2*m.sqrt(good*bad)
        failure['direct_audit'] = dict(
            digits=80, initial_energy=show(budget), energy=show(energy),
            good=show(good), defect=show(bad), certificate_margin=show(margin),
            mean_slack=show(mean), normalized_mean_slack=show(mean/budget**2),
            state_still_certified=bool(margin >= -m.mpf('1e-12')*max(1, budget)),
            mean_still_negative=bool(mean < -m.mpf('1e-12')*max(1, budget**2)),
            max_stored_energy_error=show(max_error), successors=outgoing,
            oriented={str(r): show(v) for r, v in oriented.items()})
        assert failure['direct_audit']['state_still_certified']
        assert failure['direct_audit']['mean_still_negative']


if __name__ == '__main__':
    started = time.monotonic()
    source = Path('defect-reserve-reanalysis.json')
    raw = source.read_bytes()
    data = json.loads(raw)
    workers = min(8, os.cpu_count() or 1, len(data['results']))
    with mp.Pool(workers) as pool:
        results = pool.map(inspect_cutoff, data['results'])
    failures = [f for r in results for f in r['failures']]
    worst = min((r['worst'] for r in results if r['worst'] is not None),
                key=lambda r: r['normalized_mean_slack'])
    output = dict(question='Log-weighted successor squared slack is nonnegative at every certified state with at least three unused primes.',
                  input_sha256=hashlib.sha256(raw).hexdigest(), workers=workers,
                  elapsed_seconds=time.monotonic()-started,
                  tested=sum(r['tested'] for r in results), failures=len(failures),
                  reachable_failures=sum(f['certified_predecessor_path'] is not None for f in failures),
                  first_failure=failures[0] if failures else None, worst=worst,
                  results=results)
    Path('summary.json').write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({k: v for k, v in output.items() if k not in ('results', 'worst')}, indent=2))
