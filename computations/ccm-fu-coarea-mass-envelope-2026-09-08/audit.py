"""Original time-sum, 80-digit audit. Execute only on supplied RunPod."""
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import signal
import time
import mpmath as mpf


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
    c = (-1)**len(factors)*mpf.fsum(steps[k]*D[k//d] for k in range(d,M))
    return d, c, factors


def state(coeff, P):
    F, A = {}, {}
    for d,c,factors in coeff:
        r=d
        for p in factors:
            if p in P:
                r//=p
        F.setdefault(r,[]).append(c)
        A.setdefault(r,[]).append(abs(c))
    return {r:mpf.fsum(v) for r,v in F.items()}, {r:mpf.fsum(v) for r,v in A.items()}


def quantities(F,A):
    J=mpf.fsum(F[r]**2/a for r,a in A.items() if a)
    m=max(A.values())
    return J,m,J*m


def successor(F,A,q):
    G,H={},{}
    for r,a in A.items():
        label=r//q if r%q==0 else r
        G.setdefault(label,[]).append(F[r])
        H.setdefault(label,[]).append(a)
    return {r:mpf.fsum(v) for r,v in G.items()}, {r:mpf.fsum(v) for r,v in H.items()}


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(90)
    started=time.monotonic()
    mpf.mp.dps=80
    raw=Path('summary.json').read_bytes()
    data=json.loads(raw)
    result=min((r for r in data['results'] if r['first_trap'] is not None),key=lambda r:r['M'])
    M=result['M']
    trap=result['first_trap']
    D=[mpf.mpf(0)]+[mpf.loggamma(n+1)-sum(n//d for d in range(1,n+1))+2*mpf.euler*n
                   for n in range(1,M)]
    steps=[mpf.sqrt(k+1)-mpf.sqrt(k) for k in range(M)]
    with mp.get_context('fork').Pool(4,initializer=init) as pool:
        coeff=[v for v in pool.map(coefficient,range(1,M),chunksize=16) if v is not None]
    primes=[d for d,c,f in coeff if len(f)==1]
    F,A=state(coeff,set())
    B0=quantities(F,A)[2]
    show=lambda x:mpf.nstr(x,70)
    prefix=[]
    P=[]
    all_candidates=[]
    for k in range(trap['step']+1):
        J,largest,B=quantities(F,A)
        candidates=[]
        for q in primes:
            if q in P:
                continue
            G,H=successor(F,A,q)
            J1,m1,B1=quantities(G,H)
            loss=mpf.fsum((A[r//q]*F[r]-A[r]*F[r//q])**2/
                         (A[r]*A[r//q]*(A[r]+A[r//q])) for r in A if r%q==0)
            assert abs((J-J1)-loss)<mpf.mpf('1e-65')
            candidates.append((B1,q,J1,m1))
        candidates.sort()
        B1,q,J1,m1=candidates[0]
        assert q==result['path'][k]['prime']
        prefix.append(dict(step=k,P=P.copy(),selected=q,envelope=show(B),
            gain=show(B1-B),choice_margin=show(candidates[1][0]-B1),
            head=show(F[1]),head_mass=show(A[1]),largest_mass=show(largest),
            head_slope=show(J-F[1]**2/A[1]-A[1]-2*F[1])))
        if k==trap['step']:
            assert B1-B>mpf.mpf('1e-10')*max(1,B0)
            for z,p,j,m in candidates:
                assert z-B>0
                all_candidates.append(dict(prime=p,gain=show(z-B),envelope=show(z),
                    variance_loss=show(J-j),new_largest=show(m)))
        F,A=successor(F,A,q)
        P.append(q)
    metrics=[]
    for r in data['results']:
        peak=max(r['path'],key=lambda s:s['envelope_after'])
        metrics.append(dict(M=r['M'],raw_peak_ratio=max([r['initial']['raw_energy']]+
            [s['raw_energy_after'] for s in r['path']])/r['initial']['raw_energy'],
            envelope_peak_step=peak['step'],envelope_peak_prime=peak['prime'],
            envelope_peak_ratio=r['peak_ratio'],raw_energy_at_envelope_peak=peak['raw_energy_after']))
    out=dict(M=M,digits=80,workers=4,seconds=time.monotonic()-started,
        summary_sha256=hashlib.sha256(raw).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        audited_prefix=prefix,trap_candidates=all_candidates,screen_metrics=metrics)
    Path('audit.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k not in ('trap_candidates',)}))
