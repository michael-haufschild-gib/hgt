"""Frozen complete fixed-late greedy diagnostic. Execute only on RunPod."""
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time

import numpy as np
from source_screen import source


def successor(F, q):
    G = F.copy()
    child = np.arange(q, len(F), q)
    G[child // q] += F[child]
    G[child] = 0
    return G


def path(M, primes, factors, coeff, mode):
    F = np.zeros(M)
    for d, c in coeff:
        F[d] = c
    Q0 = float(F @ F)
    lookup = {p: i for i, p in enumerate(primes)}
    edge = np.asarray([(lookup[p], n // p, n) for n, _ in coeff
                       for p in factors[n]], dtype=np.int64).T
    ei, er, en = edge
    late = [i for i, p in enumerate(primes) if 2*p > M]
    if mode == 'decreasing':
        late.reverse()
    middle = np.asarray([i for i, p in enumerate(primes) if 2*p <= M])
    remaining = np.ones(len(primes), dtype=bool)
    late_b = -F[np.asarray(primes)[late]]
    late_mass = np.append(np.cumsum(late_b[::-1])[::-1], 0.0)
    late_squares = np.append(np.cumsum((late_b**2)[::-1])[::-1], 0.0)
    nonscalar = np.asarray([n for n in range(M) if len(factors[n]) >= 2])
    li = 0
    steps, positive_states = [], []
    first_cross = None
    first_nonscalar_positive = None
    while np.any(remaining):
        Q = float(F @ F)
        gains = 2*np.bincount(ei, weights=F[er]*F[en], minlength=len(primes))
        allowed = middle[remaining[middle]].tolist()
        if li < len(late):
            allowed.append(late[li])
        allowed.sort()
        chosen = min(allowed, key=lambda i: (gains[i], primes[i]))
        q = primes[chosen]
        index = len(steps)
        scalar_count = int(np.count_nonzero(F[nonscalar]))
        positive = bool(gains[chosen] > 1e-10*max(1, Q0))
        if positive:
            positive_states.append(index)
            if scalar_count and first_nonscalar_positive is None:
                first_nonscalar_positive = index
        row = dict(index=index, prime=q, Q_before=Q, head_before=float(F[1]),
                   remaining_late_mass=float(late_mass[li]),
                   remaining_late_squares=float(late_squares[li]),
                   nonlate_nonempty=Q-float(F[1])**2-float(late_squares[li]),
                   nonscalar_active_labels=scalar_count,
                   min_allowed_gain=float(gains[chosen]), allowed_count=len(allowed),
                   next_late=primes[late[li]] if li < len(late) else None,
                   middle_count=int(np.count_nonzero(remaining[middle])))
        after = successor(F, q)
        nextQ = float(after @ after)
        assert abs(nextQ-Q-float(gains[chosen])) <= 1e-8*max(1, Q0)
        row.update(Q_after=nextQ, ratio=nextQ/Q0)
        if first_cross is None and nextQ > Q0+1e-10*max(1, Q0):
            first_cross = index
            row['allowed'] = [dict(prime=primes[i], gain=float(gains[i]),
                                   energy=Q+float(gains[i])) for i in allowed]
        steps.append(row)
        if li < len(late) and chosen == late[li]:
            li += 1
        remaining[chosen] = False
        F = after
    assert len(steps) == len(primes) and li == len(late)
    total = math.fsum(c for _, c in coeff)
    assert abs(float(F[1])-total) <= 1e-8*max(1, Q0)
    return dict(mode=mode, Q0=Q0, total=total, terminal=float(F @ F),
                peak_ratio=max([1.0]+[s['ratio'] for s in steps]),
                first_cross=first_cross, positive_states=positive_states,
                first_nonscalar_positive=first_nonscalar_positive,
                peak_post_initial=max(range(1, len(steps)), key=lambda i: steps[i]['Q_before']),
                steps=steps)


def cutoff(M):
    start = time.monotonic()
    primes, factors, coeff = source(M)
    result = dict(M=M, prime_count=len(primes), source_terms=len(coeff),
                  increasing=path(M, primes, factors, coeff, 'increasing'),
                  decreasing=path(M, primes, factors, coeff, 'decreasing'))
    old = next((r for r in json.loads(Path('baseline.json').read_text())['results']
                if r['M'] == M), None)
    if old:
        assert abs(result['increasing']['Q0']-old['Q0']) <= 1e-8*max(1, old['Q0'])
        assert abs(result['increasing']['total']-old['total']) <= 1e-8*max(1, old['Q0'])
    result['baseline_checked'] = old is not None
    result['seconds'] = time.monotonic()-start
    Path(f'cutoff_{M}.json').write_text(json.dumps(result, indent=2))
    return result


def deadline(*_):
    raise TimeoutError('Frozen90seconddeadline')


def worker_init():
    signal.signal(signal.SIGALRM, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    start = time.monotonic()
    failure = None
    try:
        with mp.get_context('fork').Pool(4, initializer=worker_init) as pool:
            results = pool.map(cutoff, [512, 2048, 8192, 32768])
    except Exception as exc:
        failure = repr(exc)
        results = [json.loads(p.read_text()) for p in sorted(Path('.').glob('cutoff_*.json'))]
    signal.alarm(0)
    out = dict(workers=4, seconds=time.monotonic()-start, failure=failure,
               script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               source_sha256=hashlib.sha256(Path('source_screen.py').read_bytes()).hexdigest(),
               baseline_sha256=hashlib.sha256(Path('baseline.json').read_bytes()).hexdigest(),
               results=results)
    Path('summary.json').write_text(json.dumps(out, indent=2))
    print(json.dumps({k:v for k,v in out.items() if k != 'results'}))
    print(json.dumps([dict(M=r['M'], seconds=r['seconds'],
                          increasing_peak=r['increasing']['peak_ratio'],
                          decreasing_peak=r['decreasing']['peak_ratio'],
                          increasing_cross=r['increasing']['first_cross'],
                          decreasing_cross=r['decreasing']['first_cross'],
                          increasing_positive=len(r['increasing']['positive_states']),
                          decreasing_positive=len(r['decreasing']['positive_states']))
                      for r in results]))
    if failure:
        raise SystemExit(2)
