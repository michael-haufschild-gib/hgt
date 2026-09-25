"""Frozen defect-supported extension diagnostic. Run only on RunPod."""
import csv
import hashlib
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import time


def graph(primes, states, budget, tol):
    full = len(states)-1
    certified = [s['phi'] <= budget+tol for s in states]
    ordinary = {0: []}
    policy = {0: []}
    failures = []
    for mask in range(full+1):
        if mask != full and not certified[mask]:
            continue
        if mask:
            for i, p in enumerate(primes):
                if not mask >> i & 1:
                    continue
                pred = mask ^ (1 << i)
                if pred in ordinary and mask not in ordinary:
                    ordinary[mask] = ordinary[pred]+[p]
                support = states[pred]['negative_support']
                if pred in policy and (not support or support >> i & 1) and mask not in policy:
                    policy[mask] = policy[pred]+[p]
        if mask == full or not states[mask]['negative_support']:
            continue
        outgoing = [(i, mask | (1 << i)) for i in range(len(primes)) if not mask >> i & 1]
        exits = [(i, nxt) for i, nxt in outgoing if nxt == full or certified[nxt]]
        support = states[mask]['negative_support']
        if not any(support >> i & 1 for i, _ in exits):
            failures.append(dict(mask=mask, ordinary_reachable=mask in ordinary,
                                 policy_reachable=mask in policy, ordinary_path=ordinary.get(mask),
                                 policy_path=policy.get(mask), outgoing=outgoing))
    return dict(failures=failures, path=policy.get(full), original_path=ordinary.get(full),
                eligible=sum(certified[i] and bool(s['negative_support']) for i, s in enumerate(states[:-1])),
                ordinary_reachable=len(ordinary), policy_reachable=len(policy))


def state(field, tol, sqrt, fsum):
    good = fsum(v*v for v in field.values() if v >= 0)
    bad = fsum(v*v for v in field.values() if v < 0)
    negatives = sorted(r for r, v in field.items() if r and v < -tol)
    support = 0
    for r in negatives:
        support |= r
    return dict(oriented=field, good=good, defect=bad, energy=good+bad,
                phi=good+bad+2*sqrt(good*bad), negative_nonempty=negatives,
                negative_support=support)


def reconstruct(record):
    saved = record['states']
    cutoff = record['M']
    primes = saved[-1]['P']
    energy = [s['energy'] for s in saved]
    full = len(saved)-1
    assert [s['mask'] for s in saved] == list(range(full+1))
    tol = 1e-12*max(1.0, energy[0])
    late = [(i, p) for i, p in enumerate(primes) if 2*p > cutoff]
    heads = []
    for mask in range(full+1):
        if late:
            i, p = late[-1]
            bit = 1 << i
            cp = -(math.sqrt(cutoff)-math.sqrt(p))*(2*0.5772156649015328606065120900824-1)
            head = ((energy[mask]-energy[mask ^ bit])/(2*cp)+cp if mask & bit
                    else (energy[mask | bit]-energy[mask])/(2*cp))
        else:
            assert full == 0
            head = math.sqrt(energy[mask])
        heads.append(head)
    coefficients = heads.copy()
    for i in range(len(primes)):
        for mask in range(full+1):
            if mask >> i & 1:
                coefficients[mask] -= coefficients[mask ^ (1 << i)]
    support = [(mask, v) for mask, v in enumerate(coefficients)
               if math.prod(p for i, p in enumerate(primes) if mask >> i & 1) < cutoff]
    states = []
    error = 0.0
    for mask in range(full+1):
        grouped = {}
        for r, v in support:
            grouped.setdefault(r & ~mask, []).append(v)
        field = {r: (-1)**bin(r).count('1')*math.fsum(vs) for r, vs in grouped.items()}
        s = state(field, tol, math.sqrt, math.fsum)
        errors = [abs(s['energy']-saved[mask]['energy']), abs(s['good']-saved[mask]['good']),
                  abs(s['defect']-saved[mask]['defect']), abs(s['phi']-saved[mask]['geometric_upper'])]
        error = max(error, *errors)
        assert max(errors) <= tol
        states.append(s)
    result = graph(primes, states, energy[0], tol)
    audit = None
    if result['failures'] or result['path'] is None:
        audit = direct_audit(cutoff, primes, states, result)
    for failure in result['failures']:
        failure['state'] = states[failure['mask']]
        failure['P'] = saved[failure['mask']]['P']
        failure['successors'] = [dict(prime=primes[i], mask=nxt, **states[nxt])
                                 for i, nxt in failure.pop('outgoing')]
    return dict(M=cutoff, primes=primes, initial_energy=energy[0], states=len(states),
                max_reconstruction_error=error, audit=audit, **result)


def direct_audit(cutoff, primes, stored, expected):
    import mpmath as m
    m.mp.dps = 80
    defect = [m.mpf(0)] + [m.fsum(m.log(j) for j in range(1, n+1))
              - sum(n//d for d in range(1, n+1))+2*m.euler*n for n in range(1, cutoff)]
    coeff = []
    for d in range(1, cutoff):
        if any(d % (p*p) == 0 for p in primes):
            continue
        label = sum(1 << i for i, p in enumerate(primes) if d % p == 0)
        value = (-1)**bin(label).count('1')*m.fsum((m.sqrt(k+1)-m.sqrt(k))*defect[k//d]
                                                for k in range(d, cutoff))
        coeff.append((label, value))
    budget = m.fsum(v*v for _, v in coeff)
    tol = m.mpf('1e-12')*max(1, budget)
    states = []
    error = m.mpf(0)
    for mask in range(len(stored)):
        grouped = {}
        for r, v in coeff:
            grouped.setdefault(r & ~mask, []).append(v)
        field = {r: (-1)**bin(r).count('1')*m.fsum(vs) for r, vs in grouped.items()}
        s = state(field, tol, m.sqrt, m.fsum)
        assert s['negative_nonempty'] == stored[mask]['negative_nonempty']
        error = max(error, abs(s['phi']-stored[mask]['phi']),
                    *(abs(v-stored[mask]['oriented'].get(r, 0)) for r, v in field.items()))
        states.append(s)
    assert graph(primes, states, budget, tol) == expected
    witnesses = []
    show = lambda v: m.nstr(v, 65)
    for failure in expected['failures']:
        chosen = [failure['mask']]+[nxt for _, nxt in failure['outgoing']]
        witnesses.append([dict(mask=mask, phi=show(states[mask]['phi']),
                               margin=show(budget-states[mask]['phi']),
                               oriented={str(r): show(v) for r, v in states[mask]['oriented'].items()})
                          for mask in chosen])
    return dict(digits=80, exhaustive_states=len(states), graph_agrees=True,
                initial_energy=show(budget), max_error=show(error), all_failure_fields=witnesses)


if __name__ == '__main__':
    started = time.monotonic()
    source, original = Path('defect-reserve-reanalysis.json'), Path('subset-states.csv')
    data = json.loads(source.read_bytes())
    energies = {(int(r['M']), int(r['mask'])): float(r['energy']) for r in csv.DictReader(original.open())}
    for record in data['results']:
        for s in record['states']:
            assert s['energy'] == energies[(record['M'], s['mask'])]
    workers = min(8, os.cpu_count() or 1, len(data['results']))
    with mp.Pool(workers) as pool:
        results = pool.map(reconstruct, data['results'])
    output = dict(question='Certified extension selecting from the union of negative nonempty labels.',
                  input_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (source, original)},
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  workers=workers, elapsed_seconds=time.monotonic()-started,
                  states=sum(r['states'] for r in results), eligible=sum(r['eligible'] for r in results),
                  failures=sum(len(r['failures']) for r in results),
                  failed_path_cutoffs=[r['M'] for r in results if r['path'] is None], results=results)
    Path('summary.json').write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'results'}, indent=2))
