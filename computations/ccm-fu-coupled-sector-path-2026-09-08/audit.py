"""Independent original-time-sum trap audit. Run only on supplied RunPod."""
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import signal
import time
import mpmath as m


def deadline(*_):
    raise TimeoutError('Frozen90secondauditdeadline')


def init():
    signal.signal(signal.SIGALRM, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


def coefficient(d):
    rem, trial, primes = d, 2, []
    while trial * trial <= rem:
        if rem % trial == 0:
            rem //= trial
            primes.append(trial)
            if rem % trial == 0:
                return None
        trial += 1
    if rem > 1:
        primes.append(rem)
    v = (-1)**len(primes) * m.fsum(steps[k] * D[k//d] for k in range(d, M))
    label = d
    for p in primes:
        if p in P:
            label //= p
    return label, v


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    start = time.monotonic()
    m.mp.dps = 80
    raw = Path('paths.json').read_bytes()
    data = json.loads(raw)
    flagged = [(r, s) for r in data['results'] for s in r['trajectory'] if s['strict_trap']]
    r, s = min(flagged, key=lambda rs: (rs[0]['M'], rs[1]['step']))
    M, P = r['M'], set(s['P'])
    print('Auditing', M, sorted(P), flush=True)
    D = [m.mpf(0)] + [m.loggamma(n+1) - sum(n//d for d in range(1, n+1))
                      + 2*m.euler*n for n in range(1, M)]
    steps = [m.sqrt(k+1)-m.sqrt(k) for k in range(M)]
    with mp.get_context('fork').Pool(4, initializer=init) as pool:
        coeff = [c for c in pool.map(coefficient, range(1, M), chunksize=16) if c is not None]
    F = {}
    for label, v in coeff:
        F.setdefault(label, []).append(v)
    F = {label: m.fsum(vs) for label, vs in F.items()}
    candidates = [q for q in range(15, M) if q*q <= M and q not in P
                  and all(q % d for d in range(2, q))]
    assert candidates == sorted(map(int, s['gains']))
    T0 = m.fsum(v*v for label, v in F.items() if label not in (1, 2))
    diagonal = m.fsum(v*v for _, v in coeff)
    show = lambda v: m.nstr(v, 70)
    results = []
    gains = {}
    for q in candidates:
        G = {}
        for label, v in F.items():
            G.setdefault(label//q if label % q == 0 else label, []).append(v)
        G = {label: m.fsum(vs) for label, vs in G.items()}
        T1 = m.fsum(v*v for label, v in G.items() if label not in (1, 2))
        gain = T1 - T0
        cross = m.fsum(-b*b if label//q in (1, 2) else 2*F.get(label//q, 0)*b
                       for label, b in F.items() if label % q == 0)
        assert abs(gain-cross) < m.mpf('1e-65')
        assert gain > m.mpf('1e-10') * max(1, diagonal)
        err = abs(gain-m.mpf(s['gains'][str(q)]))
        assert err < m.mpf('1e-10') * max(1, diagonal)
        gains[q] = gain
        results.append(dict(prime=q, gain=show(gain), transverse_after=show(T1),
                            merger_error=show(abs(gain-cross)), screen_error=show(err)))
    selected = min(candidates, key=lambda q: (gains[q], q))
    assert selected == s['selected']
    out = dict(M=M, P=sorted(P), step=s['step'], selected=selected, digits=80, workers=4,
               seconds=time.monotonic()-start, transverse_before=show(T0), diagonal=show(diagonal),
               head=show(F.get(1, 0)), two=show(F.get(2, 0)), candidates=results,
               paths_sha256=hashlib.sha256(raw).hexdigest(),
               script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('audit.json').write_text(json.dumps(out, indent=2))
    print(json.dumps(out))
