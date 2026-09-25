"""Frozen conjunction of nonempty dissipation and envelope admission; RunPod only."""
import os
os.environ.update(OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
import csv
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time


def inspect(job):
    M, energies = job
    primes = [p for p in range(2, M) if all(p % d for d in range(2, math.isqrt(p)+1))]
    size = 1 << len(primes)
    assert set(energies) == set(range(size))
    e = [energies[m] for m in range(size)]
    budget = e[0]
    tol = 1e-12 * max(1., budget)
    late = [(i,p) for i,p in enumerate(primes) if 2*p > M]
    heads, spread = [], 0.
    for mask in range(size):
        if not late:
            assert size == 1
            heads.append(math.sqrt(e[mask]))
            continue
        anchors = []
        for i,p in late:
            bit = 1 << i
            c = -(math.sqrt(M)-math.sqrt(p))*(2*0.5772156649015328606065120900824-1)
            h = ((e[mask]-e[mask ^ bit])/(2*c)+c if mask & bit
                 else (e[mask | bit]-e[mask])/(2*c))
            anchors.append(h)
        spread = max(spread, max(anchors)-min(anchors))
        heads.append(anchors[-1])
    assert spread < tol
    v = [e[m]-heads[m]**2 for m in range(size)]
    assert min(v) >= -tol
    def children(m):
        return [(p, m | (1 << i)) for i,p in enumerate(primes) if not m & (1 << i)]
    witness = [max([m]+[n for _,n in children(m)], key=lambda n:e[n]) for m in range(size)]
    env = [e[n] for n in witness]
    admitted = [x <= budget+tol for x in env]
    joint_paths = {0: []} if admitted[0] else {}
    admissible_paths = {0: []} if admitted[0] else {}
    traps, incompatible = [], []
    def record(mask):
        return dict(M=M, mask=mask, P=[p for i,p in enumerate(primes) if mask & (1 << i)],
            energy=e[mask], head=heads[mask], nonempty=v[mask], envelope=env[mask],
            budget=budget, admitted=admitted[mask], reachable_joint=mask in joint_paths,
            reachable_admitted=mask in admissible_paths,
            choices=[dict(p=p, mask=n, nonempty_gain=v[n]-v[mask], envelope=env[n],
                envelope_excess=env[n]-budget, envelope_witness=witness[n]) for p,n in children(mask)])
    for mask in range(size):
        if mask:
            for i,p in enumerate(primes):
                if mask & (1 << i):
                    prev=mask ^ (1 << i)
                    if admitted[mask] and prev in admissible_paths and mask not in admissible_paths:
                        admissible_paths[mask]=admissible_paths[prev]+[p]
                    if admitted[mask] and prev in joint_paths and v[mask] <= v[prev]+tol and mask not in joint_paths:
                        joint_paths[mask]=joint_paths[prev]+[p]
        if mask == size-1:
            continue
        choices=children(mask)
        if all(v[n] > v[mask]+tol for _,n in choices):
            traps.append(record(mask))
        if admitted[mask] and not any(admitted[n] and v[n] <= v[mask]+tol for _,n in choices):
            incompatible.append(record(mask))
    return dict(M=M,states=size,eligible=sum(admitted[:-1]),max_head_anchor_spread=spread,
        traps=traps,incompatible=incompatible,joint_complete_path=joint_paths.get(size-1),
        admitted_reachable=len(admissible_paths),joint_reachable=len(joint_paths))


def audit(record):
    import mpmath as m
    m.mp.dps=80
    M=record['M']
    primes=[p for p in range(2,M) if all(p%d for d in range(2,math.isqrt(p)+1))]
    defect=[m.mpf(0)]+[m.fsum(m.log(j) for j in range(1,k+1))-sum(k//d for d in range(1,k+1))
        +2*m.euler*k for k in range(1,M)]
    coeff=[]
    for d in range(1,M):
        if any(d%(p*p)==0 for p in primes):continue
        mask=sum(1<<i for i,p in enumerate(primes) if d%p==0)
        c=(-1)**bin(mask).count('1')*m.fsum((m.sqrt(k+1)-m.sqrt(k))*defect[k//d] for k in range(d,M))
        coeff.append((d,mask,c))
    cache={}
    def field(mask):
        if mask not in cache:
            bins={}
            for _,support,c in coeff:bins.setdefault(support & ~mask,[]).append(c)
            f={r:m.fsum(xs) for r,xs in bins.items()}
            e=m.fsum(x*x for x in f.values())
            cache[mask]=(e,f.get(0,m.mpf(0)),m.fsum(x*x for r,x in f.items() if r),f)
        return cache[mask]
    def children(mask):return [(p,mask|(1<<i)) for i,p in enumerate(primes) if not mask&(1<<i)]
    def envelope(mask):
        return max([(field(mask)[0],None,mask)]+[(field(n)[0],p,n) for p,n in children(mask)],key=lambda t:t[0])
    mask=record['mask']; budget=field(0)[0]; current=field(mask)
    show=lambda x:m.nstr(x,70)
    candidates=[]
    for p,n in children(mask):
        en,w,wstate=envelope(n)
        gain=field(n)[2]-current[2]
        candidates.append(dict(p=p,nonempty_gain=show(gain),envelope_excess=show(en-budget),
            envelope_witness=w,envelope_state=wstate,nonempty_decreases=bool(gain<=0),
            preserves_admission=bool(en<=budget),joint_success=bool(gain<=0 and en<=budget)))
    en,w,_=envelope(mask)
    assert abs(current[0]-record['energy']) < m.mpf('1e-10')
    assert abs(current[2]-record['nonempty']) < m.mpf('1e-10')
    return dict(M=M,P=record['P'],mask=mask,budget=show(budget),energy=show(current[0]),
        head=show(current[1]),nonempty=show(current[2]),envelope=show(en),
        admission_margin=show(budget-en),admitted=bool(en<=budget),envelope_witness=w,
        genuine_nonempty_trap=all(not x['nonempty_decreases'] for x in candidates),
        genuine_joint_failure=bool(en<=budget and all(not x['joint_success'] for x in candidates)),
        candidates=candidates,
        fields=[dict(mask=ms,energy=show(e),head=show(h),nonempty=show(v),
            values=[dict(label=[p for i,p in enumerate(primes) if r&(1<<i)],value=show(c))
                    for r,c in sorted(f.items())]) for ms,(e,h,v,f) in sorted(cache.items())],
        coefficients=[dict(d=d,support=[p for i,p in enumerate(primes) if r&(1<<i)],value=show(c))
                      for d,r,c in coeff])


def deadline(_sig,_frame):raise TimeoutError('Frozen fifty-second deadline')
def initialize():
    signal.signal(signal.SIGTERM,signal.SIG_DFL)
    signal.signal(signal.SIGALRM,signal.SIG_DFL)


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline);signal.signal(signal.SIGTERM,deadline);signal.alarm(50)
    start=time.monotonic();rows={};source=Path('subset-states.csv')
    with source.open() as handle:
        for r in csv.DictReader(handle):rows.setdefault(int(r['M']),{})[int(r['mask'])]=float(r['energy'])
    assert sorted(rows)==list(range(1,33))
    workers=min(8,os.cpu_count() or 1)
    with mp.Pool(workers,initializer=initialize) as pool:results=pool.map(inspect,sorted(rows.items()))
    first_trap=next((f for r in results for f in r['traps']),None)
    first_joint=next((f for r in results for f in r['incompatible']),None)
    targets={(r['M'],r['mask']):r for r in [first_trap,first_joint] if r is not None}
    with mp.Pool(workers,initializer=initialize) as pool:audits=pool.map(audit,list(targets.values()))
    out=dict(question='Every admitted actual state has a V-nonincreasing successor preserving admission.',
        workers=workers,elapsed_seconds=time.monotonic()-start,
        input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        states=sum(r['states'] for r in results),eligible=sum(r['eligible'] for r in results),
        nonempty_traps=sum(len(r['traps']) for r in results),
        joint_failures=sum(len(r['incompatible']) for r in results),
        first_nonempty_trap=first_trap,first_joint_failure=first_joint,
        complete_joint_path_failures=[r['M'] for r in results if r['joint_complete_path'] is None],
        results=results,audits=audits)
    Path('summary.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('results','audits')},indent=2))
    signal.alarm(0)
