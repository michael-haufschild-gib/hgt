"""Frozen independent original time-sum audit. Execute only on RunPod."""
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import signal
import time
import mpmath as mf


def deadline(*_):
    raise TimeoutError('Frozen90secondauditdeadline')


def init():
    signal.signal(signal.SIGALRM, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


def coefficient(d):
    n, p, factors = d, 2, []
    while p*p <= n:
        if n % p == 0:
            n //= p
            factors.append(p)
            if n % p == 0:
                return None
        p += 1
    if n > 1:
        factors.append(n)
    return d, (-1)**len(factors)*mf.fsum(steps[k]*D[k//d] for k in range(d, M)), factors


def state(coeff, processed):
    groups = {}
    for d, c, factors in coeff:
        r = d
        for p in factors:
            if p in processed:
                r //= p
        groups.setdefault(r, []).append(c)
    return {r: mf.fsum(v) for r, v in groups.items()}


def successor(field, q):
    groups = {}
    for r, c in field.items():
        label = r//q if r % q == 0 else r
        groups.setdefault(label, []).append(c)
    return {r: mf.fsum(v) for r, v in groups.items()}


def energy(field):
    return mf.fsum(v*v for v in field.values())


def show(x):
    return mf.nstr(x, 70)


def candidate(q):
    after = successor(F, q)
    result = energy(after)
    scalar_gain = 2*F.get(1, 0)*F.get(q, 0)
    return dict(prime=q, energy=result, gain=result-Q, head_increment=F.get(q, 0),
                head_product=scalar_gain, nonhead_products=result-Q-scalar_gain)


def select(data):
    ordered = [(r, mode, r[mode]) for r in sorted(data['results'], key=lambda r: r['M'])
               for mode in ['increasing', 'decreasing']]
    for result, mode, path in ordered:
        if path['first_cross'] is not None:
            return result, mode, path, path['first_cross'], 'first crossing at smallest failing cutoff'
    for result, mode, path in ordered:
        for row in path['steps']:
            if row['min_allowed_gain'] > 0 and row['nonscalar_active_labels'] > 0:
                return result, mode, path, row['index'], 'first positive minimum with active nonscalar labels'
    result, mode, path = ordered[-2]
    choices = [(row['Q_before'], mode, row['index'])
               for mode in ['increasing', 'decreasing'] for row in result[mode]['steps'][1:]]
    _, mode, index = max(choices, key=lambda x: (x[0], x[1] == 'increasing'))
    return result, mode, result[mode], index, 'largest post-initial state with a successor at largest cutoff'


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    start = time.monotonic()
    mf.mp.dps = 80
    raw = Path('summary.json').read_bytes()
    result, mode, path, index, reason = select(json.loads(raw))
    M = result['M']
    chosen = path['steps'][index]
    P = {row['prime'] for row in path['steps'][:index]}
    # Original finite time sum, independent of screen's telescoped source.
    D = [mf.mpf(0)]+[mf.loggamma(n+1)-sum(n//d for d in range(1, n+1))+2*mf.euler*n
                     for n in range(1, M)]
    steps = [mf.sqrt(k+1)-mf.sqrt(k) for k in range(M)]
    with mp.get_context('fork').Pool(4, initializer=init) as pool:
        coeff = [v for v in pool.map(coefficient, range(1, M), chunksize=16) if v is not None]
    F = state(coeff, P)
    Q, Q0 = energy(F), mf.fsum(c*c for d, c, f in coeff)
    primes = [d for d, c, f in coeff if len(f) == 1]
    remaining_late = [p for p in primes if p not in P and 2*p > M]
    middle = [p for p in primes if p not in P and 2*p <= M]
    late = chosen['next_late']
    allowed = sorted(middle+([late] if late is not None else []))
    assert len(allowed) == chosen['allowed_count']
    with mp.get_context('fork').Pool(4, initializer=init) as pool:
        candidates = pool.map(candidate, allowed, chunksize=1)
    candidates.sort(key=lambda v: (v['energy'], v['prime']))
    selected = next(v for v in candidates if v['prime'] == chosen['prime'])
    q = chosen['prime'] if chosen['prime'] in middle else next(
        v['prime'] for v in candidates if v['prime'] in middle)
    cofactors = []
    for child in sorted(F):
        if child % q != 0 or F[child] == 0:
            continue
        r = child//q
        a, b = F.get(r, mf.mpf(0)), F[child]
        cofactors.append(dict(r=r, parent=a, child=b, gain=2*a*b))
    gain = next(v['gain'] for v in candidates if v['prime'] == q)
    assert abs(gain-mf.fsum(v['gain'] for v in cofactors)) < mf.mpf('1e-65')
    late_mass = -mf.fsum(F[p] for p in remaining_late)
    late_squares = mf.fsum(F[p]**2 for p in remaining_late)
    nonlate = mf.fsum(v*v for r, v in F.items() if r != 1 and r not in remaining_late)
    assert abs(Q-F[1]**2-late_squares-nonlate) < mf.mpf('1e-65')
    assert abs(Q-mf.mpf(chosen['Q_before'])) < mf.mpf('1e-8')*max(1, Q0)
    assert abs(selected['energy']-mf.mpf(chosen['Q_after'])) < mf.mpf('1e-8')*max(1, Q0)
    assert selected['prime'] == candidates[0]['prime']
    out = dict(M=M, policy=mode, index=index, P=sorted(P), reason=reason,
               digits=80, workers=4, seconds=time.monotonic()-start,
               selected=selected['prime'], allowed_count=len(allowed), next_late=late,
               Q0=show(Q0), Q_before=show(Q), Q_after=show(selected['energy']),
               head=show(F[1]), remaining_late_mass=show(late_mass),
               remaining_late_squares=show(late_squares), nonlate_nonempty=show(nonlate),
               minimum_gain=show(candidates[0]['gain']),
               minimum_margin=show(candidates[1]['energy']-candidates[0]['energy']) if len(candidates)>1 else None,
               all_allowed_gains_positive=all(v['gain'] > 0 for v in candidates),
               selected_minimum_gap=show(selected['energy']-candidates[0]['energy']),
               nonscalar_active_labels=sum(r > 1 and r not in primes and v != 0 for r, v in F.items()),
               cofactor_prime=q,
               cofactors=[{k: (v if k == 'r' else show(v)) for k, v in row.items()} for row in cofactors],
               candidates=[{k: (v if k == 'prime' else show(v)) for k, v in row.items()} for row in candidates],
               summary_sha256=hashlib.sha256(raw).hexdigest(),
               script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('audit.json').write_text(json.dumps(out, indent=2))
    signal.alarm(0)
    print(json.dumps({k: v for k, v in out.items() if k not in ('cofactors', 'candidates')}))
