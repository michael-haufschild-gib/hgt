"""Original time-sum arity audit. Run only on the supplied RunPod."""
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
    return d, (-1)**len(factors)*mf.fsum(steps[k]*defect[k//d] for k in range(d, M)), factors


def state(processed):
    groups = {}
    for d, c, factors in coeff:
        r = d
        for p in factors:
            if p in processed:
                r //= p
        groups.setdefault(r, []).append(c)
    return {r: mf.fsum(v) for r, v in groups.items()}


def successor(F, q):
    groups = {}
    for r, c in F.items():
        label = r//q if r % q == 0 else r
        groups.setdefault(label, []).append(c)
    return {r: mf.fsum(v) for r, v in groups.items()}


def arity(F):
    return mf.fsum(degree[r]*v*v for r, v in F.items())


def contributions(F, q):
    out = []
    for child in sorted(F):
        if child % q != 0 or F[child] == 0:
            continue
        r = child//q
        a, b = F.get(r, mf.mpf(0)), F[child]
        out.append(dict(r=r, degree=degree[r], parent=a, child=b,
                        J=2*degree[r]*a*b, W=b*b))
    return out


def show(x):
    return mf.nstr(x, 70)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    started = time.monotonic()
    mf.mp.dps = 80
    raw, oldraw = Path('summary.json').read_bytes(), Path('paths.json').read_bytes()
    results, paths = json.loads(raw)['results'], json.loads(oldraw)['results']
    chosen = None
    for reason in ['first_positive_cumulative_J', 'first_positive_D', 'first_interacting']:
        for result in sorted(results, key=lambda x:x['M']):
            for mode in ['increasing','decreasing']:
                index = result[mode][reason]
                if index is not None:
                    chosen = (result, mode, index, reason)
                    break
            if chosen:
                break
        if chosen:
            break
    result, mode, index, reason = chosen
    M = result['M']
    path = next(r for r in paths if r['M']==M)[mode]['steps']
    P = {r['prime'] for r in path[:index]}
    q = path[index]['prime']
    defect = [mf.mpf(0)]+[mf.loggamma(n+1)-sum(n//d for d in range(1,n+1))+2*mf.euler*n
                         for n in range(1,M)]
    steps = [mf.sqrt(k+1)-mf.sqrt(k) for k in range(M)]
    with mp.get_context('fork').Pool(4, initializer=init) as pool:
        coeff = [v for v in pool.map(coefficient, range(1,M), chunksize=16) if v is not None]
    degree = {d:len(factors) for d,c,factors in coeff}
    F = state(P)
    D0 = mf.fsum(degree[d]*c*c for d,c,factors in coeff)
    before, after = arity(F), arity(successor(F,q))
    cells = contributions(F,q)
    J, W = mf.fsum(r['J'] for r in cells), mf.fsum(r['W'] for r in cells)
    assert abs(after-before-J+W)<mf.mpf('1e-65')
    assert abs(after-mf.mpf(result[mode]['steps'][index]['D_after']))<mf.mpf('1e-8')*max(1,D0)
    cumulative = None
    if reason == 'first_positive_cumulative_J':
        current, cumulative, totalW = state(set()), mf.mpf(0), mf.mpf(0)
        for step in path[:index+1]:
            rows = contributions(current,step['prime'])
            cumulative += mf.fsum(r['J'] for r in rows)
            totalW += mf.fsum(r['W'] for r in rows)
            current = successor(current,step['prime'])
        assert abs(arity(current)-D0-cumulative+totalW)<mf.mpf('1e-65')
        assert cumulative>0
    elif reason == 'first_positive_D':
        assert after>before
    out = dict(M=M, policy=mode, index=index, P=sorted(P), prime=q, reason=reason,
               digits=80, workers=4, seconds=time.monotonic()-started,
               D0=show(D0), D_before=show(before), D_after=show(after), gain=show(after-before),
               J=show(J), W=show(W), cumulative_J=show(cumulative) if cumulative is not None else None,
               Q_before=show(mf.fsum(v*v for v in F.values())),
               Q_after=show(mf.fsum(v*v for v in successor(F,q).values())),
               cofactors=[{k:(v if k in ['r','degree'] else show(v)) for k,v in r.items()} for r in cells],
               summary_sha256=hashlib.sha256(raw).hexdigest(), paths_sha256=hashlib.sha256(oldraw).hexdigest(),
               script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('audit.json').write_text(json.dumps(out,indent=2))
    signal.alarm(0)
    print(json.dumps(out))
