"""Frozen complete-field sign-class diagnostic. Execute only on RunPod."""
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
    valid = [certified[i] and not s['negative_nonempty'] for i, s in enumerate(states)]
    reach = {0: []} if valid[0] else {}
    optimum = {0: (len(states[0]['negative_nonempty']), [])} if certified[0] else {}
    for mask in range(1, full+1):
        predecessors = [(mask ^ (1 << i), p) for i, p in enumerate(primes) if mask >> i & 1]
        if mask == full or valid[mask]:
            for pred, p in predecessors:
                if pred in reach:
                    reach[mask] = reach[pred]+[p]
                    break
        if mask == full or certified[mask]:
            candidates = [(max(optimum[pred][0], len(states[mask]['negative_nonempty'])),
                           optimum[pred][1]+[p]) for pred, p in predecessors if pred in optimum]
            if candidates:
                optimum[mask] = min(candidates)
    failures = []
    for mask in range(full):
        if not valid[mask]:
            continue
        outgoing = [(p, mask | (1 << i)) for i, p in enumerate(primes) if not mask >> i & 1]
        if not any(nxt == full or valid[nxt] for _, nxt in outgoing):
            failures.append(dict(mask=mask, reachable=mask in reach,
                                 predecessor_path=reach.get(mask), outgoing=outgoing))
    return dict(path=reach.get(full), optimum=optimum.get(full), failures=failures,
                certified=sum(certified), admissible=sum(valid), reachable=len(reach))


def inspect_cutoff(record):
    cutoff = record['M']
    saved = record['states']
    energy = [s['energy'] for s in saved]
    assert [s['mask'] for s in saved] == list(range(len(saved)))
    primes = saved[-1]['P']
    full = len(saved)-1
    budget = energy[0]
    tol = 1e-12*max(1.0, budget)
    d1 = 2*0.5772156649015328606065120900824-1
    late = [(i, p) for i, p in enumerate(primes) if 2*p > cutoff]
    heads = []
    for mask in range(full+1):
        if late:
            i, p = late[-1]
            bit = 1 << i
            cp = -(math.sqrt(cutoff)-math.sqrt(p))*d1
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
    support = [(mask, value) for mask, value in enumerate(coefficients)
               if math.prod(p for i, p in enumerate(primes) if mask >> i & 1) < cutoff]
    states = []
    max_error = 0.0
    for mask in range(full+1):
        grouped = {}
        for label, value in support:
            grouped.setdefault(label & ~mask, []).append(value)
        oriented = {r: (-1)**bin(r).count('1')*math.fsum(vs) for r, vs in grouped.items()}
        good = math.fsum(v*v for v in oriented.values() if v >= 0)
        bad = math.fsum(v*v for v in oriented.values() if v < 0)
        phi = good+bad+2*math.sqrt(good*bad)
        errors = [abs(good+bad-energy[mask]), abs(good-saved[mask]['good']),
                  abs(bad-saved[mask]['defect']), abs(phi-saved[mask]['geometric_upper'])]
        max_error = max(max_error, *errors)
        assert max(errors) <= tol
        states.append(dict(mask=mask, P=saved[mask]['P'], energy=good+bad, good=good,
                           defect=bad, phi=phi, margin=budget-phi,
                           negative_nonempty=sorted(r for r, v in oriented.items() if r and v < -tol),
                           oriented=oriented))
    result = graph(primes, states, budget, tol)
    failure_masks = [f['mask'] for f in result['failures']]
    audit = None
    if result['path'] is None or failure_masks:
        audit = direct_audit(cutoff, primes, states, budget, result)
    for failure in result['failures']:
        failure['state'] = states[failure['mask']]
        failure['successors'] = [dict(prime=p, **states[nxt]) for p, nxt in failure.pop('outgoing')]

    def path_states(path):
        if path is None:
            return None
        mask = 0
        out = [states[0]]
        for p in path:
            mask |= 1 << primes.index(p)
            out.append(states[mask])
        return out

    return dict(M=cutoff, primes=primes, initial_energy=budget, states=len(states),
                max_reconstruction_error=max_error, **result,
                path_states=path_states(result['path']),
                optimum_path_states=path_states(result['optimum'][1]) if result['optimum'] else None,
                direct_audit=audit)


def direct_audit(cutoff, primes, stored, stored_budget, expected):
    """Independent direct source; exhaustive high-precision graph at every failed cutoff."""
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
    max_error = abs(budget-stored_budget)
    for mask in range(len(stored)):
        grouped = {}
        for label, value in coeff:
            grouped.setdefault(label & ~mask, []).append(value)
        oriented = {r: (-1)**bin(r).count('1')*m.fsum(vs) for r, vs in grouped.items()}
        good = m.fsum(v*v for v in oriented.values() if v >= 0)
        bad = m.fsum(v*v for v in oriented.values() if v < 0)
        phi = good+bad+2*m.sqrt(good*bad)
        max_error = max(max_error, abs(phi-stored[mask]['phi']),
                        *(abs(v-stored[mask]['oriented'].get(r, 0)) for r, v in oriented.items()))
        negatives = sorted(r for r, v in oriented.items() if r and v < -tol)
        assert negatives == stored[mask]['negative_nonempty']
        states.append(dict(phi=phi, negative_nonempty=negatives, oriented=oriented))
    actual = graph(primes, states, budget, tol)
    assert actual == expected
    show = lambda x: m.nstr(x, 65)
    witness = None
    if expected['failures']:
        fail = expected['failures'][0]
        chosen = [fail['mask']]+[nxt for _, nxt in fail['outgoing']]
        witness = [dict(mask=mask, phi=show(states[mask]['phi']),
                        margin=show(budget-states[mask]['phi']),
                        oriented={str(r): show(v) for r, v in states[mask]['oriented'].items()})
                   for mask in chosen]
    return dict(digits=80, exhaustive_states=len(states), graph_agrees=True,
                initial_energy=show(budget), max_source_error=show(max_error),
                first_extension_failure_fields=witness)


if __name__ == '__main__':
    started = time.monotonic()
    source = Path('defect-reserve-reanalysis.json')
    raw = source.read_bytes()
    data = json.loads(raw)
    # Check the saved-energy input independently against the geometric-state records.
    original = Path('subset-states.csv')
    energies = {(int(r['M']), int(r['mask'])): float(r['energy'])
                for r in csv.DictReader(original.open())}
    for record in data['results']:
        for state in record['states']:
            assert state['energy'] == energies[(record['M'], state['mask'])]
    workers = min(8, os.cpu_count() or 1, len(data['results']))
    with mp.Pool(workers) as pool:
        results = pool.map(inspect_cutoff, data['results'])
    output = dict(question='Complete certified paths and universal extension with no negative nonempty oriented coordinates.',
                  input_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (source, original)},
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  workers=workers, elapsed_seconds=time.monotonic()-started,
                  states=sum(r['states'] for r in results),
                  failed_path_cutoffs=[r['M'] for r in results if r['path'] is None],
                  extension_failures=sum(len(r['failures']) for r in results),
                  reachable_extension_failures=sum(f['reachable'] for r in results for f in r['failures']),
                  minimum_required_nonempty_defects={r['M']: r['optimum'][0] if r['optimum'] else None for r in results},
                  results=results)
    Path('summary.json').write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'results'}, indent=2))
