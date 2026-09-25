"""Independent frozen time-sum/path audit. Execute only on supplied RunPod."""
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


def factors(d):
    rest, p, out = d, 2, []
    while p*p <= rest:
        if rest % p == 0:
            out.append(p)
            rest //= p
            if rest % p == 0:
                return None
        p += 1
    if rest > 1:
        out.append(rest)
    return out


def state(P):
    groups = {}
    for label, c in coeff:
        groups.setdefault(label & ~P, []).append(c)
    field = {r:mf.fsum(v) for r,v in groups.items()}
    Q = mf.fsum(v*v for v in field.values())
    D = mf.fsum(bin(r).count('1')*v*v for r,v in field.items())
    W = [mf.fsum(v*v for r,v in field.items() if r & (1<<j)) for j in range(len(primes))]
    J = [2*mf.fsum((bin(r).count('1')-1)*field.get(r^(1<<j),mf.mpf(0))*v
                  for r,v in field.items() if r & (1<<j)) for j in range(len(primes))]
    return P,Q,D,W,J,field.get(0,mf.mpf(0))


def show(x):
    return mf.nstr(x,70)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(90)
    started = time.monotonic()
    mf.mp.dps = 80
    raw = Path('summary.json').read_bytes()
    summary = json.loads(raw)
    assert summary['failure'] is None and len(summary['results']) == 47
    failures = [r for r in summary['results'] if not r['feasible']]
    chosen = failures[0] if failures else summary['results'][-1]
    M, primes = chosen['M'], chosen['primes']
    assert primes == [p for p in range(2,M) if all(p%d for d in range(2,p))]
    defect = [mf.mpf(0)] + [mf.loggamma(k+1)-sum(k//d for d in range(1,k+1))+2*mf.euler*k
                            for k in range(1,M)]
    steps = [mf.sqrt(k+1)-mf.sqrt(k) for k in range(M)]
    coeff = []
    for d in range(1,M):
        fs = factors(d)
        if fs is not None:
            label = sum(1<<primes.index(p) for p in fs)
            c = (-1)**len(fs)*mf.fsum(steps[k]*defect[k//d] for k in range(d,M))
            coeff.append((label,c))
    P0,Q0,D0,*_ = state(0)
    tol = mf.mpf('1e-65')*max(1,Q0,D0)
    if failures:
        size = 1<<len(primes)
        with mp.get_context('fork').Pool(4,initializer=init) as pool:
            states = pool.map(state,range(size),chunksize=64)
        cost = [mf.inf]*size
        cost[0] = mf.mpf(0)
        for P in range(1,size):
            _,Q,D,_,_,_ = states[P]
            if Q > Q0+tol:
                continue
            proposed = [cost[P^(1<<j)]+states[P^(1<<j)][3][j]
                        for j in range(len(primes)) if P & (1<<j)]
            best = min(proposed)
            if D+best <= D0+tol:
                cost[P] = best
        feasible = bool(mf.isfinite(cost[-1]))
        Path('audit_states.json').write_text(json.dumps([
            dict(P=s[0],Q=show(s[1]),D=show(s[2]),W=[show(w) for w in s[3]],
                 cost=show(cost[s[0]])) for s in states]))
        out = dict(M=M,selection='smallest_failure',feasible=feasible,
                   reachable=sum(mf.isfinite(c) for c in cost),subsets=size)
        assert not feasible
    else:
        masks = [s['P'] for s in chosen['steps']]+[(1<<len(primes))-1]
        with mp.get_context('fork').Pool(4,initializer=init) as pool:
            states = pool.map(state,masks)
        cumulativeW, cumulativeJ, rows = mf.mpf(0),mf.mpf(0),[]
        for k,step in enumerate(chosen['steps']):
            P,Q,D,W,J,head = states[k]
            nxt,Qnext,Dnext,_,_,nexthead = states[k+1]
            j = primes.index(step['prime'])
            assert nxt == P | (1<<j)
            assert abs(Dnext-D-J[j]+W[j]) < tol
            cumulativeW += W[j]
            cumulativeJ += J[j]
            assert abs(Dnext-D0+cumulativeW-cumulativeJ) < tol
            assert Qnext <= Q0+tol and cumulativeJ <= tol
            rows.append(dict(index=k,P=P,prime=step['prime'],Q=show(Qnext),D=show(Dnext),
                             W=show(W[j]),J=show(J[j]),cumulative_W=show(cumulativeW),
                             cumulative_J=show(cumulativeJ),head=show(nexthead)))
        total = mf.fsum(c for label,c in coeff)
        assert abs(states[-1][-1]-total)<tol
        assert abs(states[-1][1]-total*total)<tol and abs(states[-1][2])<tol
        out = dict(M=M,selection='largest_success_witness',feasible=True,
                   order=[s['prime'] for s in chosen['steps']],steps=rows,
                   final_head=show(total),final_head_square=show(total*total))
    out.update(digits=80,workers=4,seconds=time.monotonic()-started,Q0=show(Q0),D0=show(D0),
        summary_sha256=hashlib.sha256(raw).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('audit.json').write_text(json.dumps(out,indent=2))
    signal.alarm(0)
    print(json.dumps({k:v for k,v in out.items() if k!='steps'}))
