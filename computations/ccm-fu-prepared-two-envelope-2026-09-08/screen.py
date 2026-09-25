"""Frozen all-core prime-two diagnostic; run only on supplied RunPod."""
import os
os.environ.update(OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time
import numpy as np

CORE = {3, 5, 7, 11, 13}


def primes_below(M):
    return [p for p in range(2, M) if all(p % d for d in range(2, math.isqrt(p)+1))]


def inspect(M):
    primes = primes_below(M)
    free = [p for p in primes if p not in CORE]
    bit = {p: 1 << i for i, p in enumerate(free)}
    defect = [0.] + [math.lgamma(k+1) - sum(k//d for d in range(1,k+1))
                         + 2*0.577215664901532860606512090082402431*k for k in range(1,M)]
    step = [math.sqrt(k+1)-math.sqrt(k) for k in range(M)]
    field, diagonal = {}, 0.
    for d in range(1,M):
        if any(d % (p*p) == 0 for p in primes):
            continue
        factors = [p for p in primes if d % p == 0]
        coeff = (-1)**len(factors) * math.fsum(step[k]*defect[k//d] for k in range(d,M))
        diagonal += coeff*coeff
        label = sum(bit[p] for p in factors if p in bit)
        field[label] = field.get(label,0.) + coeff
    size = 1 << len(free)
    energy = np.zeros(size)
    for r, a in field.items():
        for s, b in field.items():
            energy[r ^ s] += a*b
    for i in range(len(free)):
        view = energy.reshape(-1,2,1 << i)
        view[:,1,:] += view[:,0,:]
    ids = np.arange(size)
    envelope = energy.copy()
    witness = ids.copy()
    for i in range(len(free)):
        targets = ids | (1 << i)
        better = energy[targets] > envelope
        witness[better] = targets[better]
        envelope = np.maximum(envelope, energy[targets])
    parents = ids[(ids & bit[2]) == 0]
    children = parents | bit[2]
    margins = envelope[children] - envelope[parents]
    tol = 1e-11*max(1.,diagonal)
    bad = np.flatnonzero(margins > tol)
    def record(j):
        parent, child = int(parents[j]), int(children[j])
        after_witness = int(witness[child])
        return dict(mask=parent, P=sorted(CORE | {p for p in free if parent & bit[p]}),
            before=float(envelope[parent]), after=float(envelope[child]), excess=float(margins[j]),
            post_two_energy=float(energy[child]),
            successor=next((p for p in free if (after_witness ^ child) == bit[p]),None),
            admitted_original=bool(envelope[parent] <= diagonal+tol),
            violates_original=bool(envelope[child] > diagonal+tol))
    return dict(M=M,free_primes=free,states=len(parents),diagonal=diagonal,
        violations=len(bad),first=None if not len(bad) else record(int(bad[0])),
        worst=record(int(np.argmax(margins))),
        admitted_original=int(np.count_nonzero(envelope[parents] <= diagonal+tol)),
        original_budget_failures=int(np.count_nonzero((envelope[parents] <= diagonal+tol)&
            (envelope[children] > diagonal+tol))))


def audit(M, record):
    import mpmath as m
    m.mp.dps = 80
    primes = primes_below(M)
    P = set(record['P'])
    defect = [m.mpf(0)] + [m.fsum(m.log(j) for j in range(1,k+1))
        -sum(k//d for d in range(1,k+1))+2*m.euler*k for k in range(1,M)]
    coeffs=[]
    for d in range(1,M):
        if any(d % (p*p) == 0 for p in primes):
            continue
        factors = frozenset(p for p in primes if d % p == 0)
        v=(-1)**len(factors)*m.fsum((m.sqrt(k+1)-m.sqrt(k))*defect[k//d] for k in range(d,M))
        coeffs.append((factors,v))
    cache={}
    def field(S):
        key=tuple(sorted(S))
        if key not in cache:
            bins={}
            for factors,v in coeffs:
                bins.setdefault(tuple(sorted(factors-S)),[]).append(v)
            values={r:m.fsum(vs) for r,vs in bins.items()}
            cache[key]=(m.fsum(v*v for v in values.values()),values)
        return cache[key]
    def env(S):
        cases=[(None,field(S)[0])]+[(q,field(S|{q})[0]) for q in primes if q not in S]
        return max(cases,key=lambda x:x[1]),cases
    (before_q,before),cases_before=env(P)
    (after_q,after),cases_after=env(P|{2})
    assert after-before > m.mpf('1e-30')
    assert abs((after-before)-record['excess']) < m.mpf('1e-8')
    repairs=[]
    for q in primes:
        if q not in P|{2}:
            (w,e),_=env(P|{2,q})
            repairs.append(dict(prime=q,witness=w,envelope=m.nstr(e,70),
                excess=m.nstr(e-before,70),restores_parent=bool(e<=before)))
    show=lambda x:m.nstr(x,70)
    return dict(M=M,P=sorted(P),before_witness=before_q,after_witness=after_q,
        before=show(before),after=show(after),excess=show(after-before),
        before_cases=[dict(q=q,energy=show(e)) for q,e in cases_before],
        after_cases=[dict(q=q,energy=show(e)) for q,e in cases_after],repairs=repairs,
        fields=[dict(P=list(key),energy=show(e),fibres=[dict(label=list(r),value=show(v))
            for r,v in sorted(f.items())]) for key,(e,f) in sorted(cache.items())],
        coefficients=[dict(support=sorted(r),value=show(v)) for r,v in coeffs])


def deadline(_sig,_frame):
    raise TimeoutError('Frozen 50-second deadline')


def initialize():
    signal.signal(signal.SIGTERM,signal.SIG_DFL)
    signal.signal(signal.SIGALRM,signal.SIG_DFL)


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(50)
    start=time.monotonic()
    workers=min(8,os.cpu_count() or 1)
    with mp.Pool(workers,initializer=initialize) as pool:
        results=pool.map(inspect,range(16,97))
    first=next((r for r in results if r['violations']),None)
    exact=None if first is None else audit(first['M'],first['first'])
    output=dict(question='Prepared-core insertion of two preserves the complete successor envelope.',
        workers=workers,elapsed_seconds=time.monotonic()-start,
        states=sum(r['states'] for r in results),violations=sum(r['violations'] for r in results),
        original_budget_failures=sum(r['original_budget_failures'] for r in results),
        first_failure=None if first is None else dict(M=first['M'],**first['first']),
        audit=exact,results=results,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('summary.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k not in ('results','audit')},indent=2))
    signal.alarm(0)
