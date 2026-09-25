"""Frozen coupled-sector steepest path. Run only on supplied RunPod."""
import collections
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time
from source_screen import source


def path(M):
    primes,factors,coeff=source(M)
    P={3,5,7,11,13}
    grouped=collections.defaultdict(list)
    for d,c in coeff:
        r=d
        for p in factors[d]:
            if p in P:r//=p
        grouped[r].append(c)
    F={r:math.fsum(vs) for r,vs in grouped.items()}
    initialT=math.fsum(v*v for r,v in F.items() if r not in (1,2))
    diagonal=math.fsum(v*v for _,v in coeff)
    tol=1e-10*max(1,diagonal)
    candidates={p for p in primes if p>=15 and p*p<=M}
    trajectory=[]
    positive=0.0
    while candidates:
        terms={q:[] for q in candidates}
        for r,b in F.items():
            for q in factors[r]:
                if q not in candidates:continue
                s=r//q
                terms[q].append(-b*b if s in (1,2) else 2*F.get(s,0.0)*b)
        gains={q:math.fsum(vs) for q,vs in terms.items()}
        q=min(candidates,key=lambda p:(gains[p],p))
        G=collections.defaultdict(list)
        for r,v in F.items():G[r//q if r%q==0 else r].append(v)
        G={r:math.fsum(vs) for r,vs in G.items()}
        T0=math.fsum(v*v for r,v in F.items() if r not in (1,2))
        T1=math.fsum(v*v for r,v in G.items() if r not in (1,2))
        assert abs(T1-T0-gains[q])<=tol
        positive+=max(gains[q],0.0)
        trajectory.append(dict(step=len(trajectory),P=sorted(P),selected=q,gain=gains[q],
            gains=gains,strict_trap=min(gains.values())>tol,transverse=T0,
            transverse_after=T1,head=F.get(1,0),two=F.get(2,0),
            positive_cost=positive))
        F=G
        P.add(q)
        candidates.remove(q)
    return dict(M=M,diagonal=diagonal,initial_transverse=initialT,
        positive_cost=positive,positive_ratio=positive/initialT,
        cumulative_budget_pass=positive<=initialT+tol,
        steps=len(trajectory),strict_traps=sum(s['strict_trap'] for s in trajectory),trajectory=trajectory)


def deadline(*_):raise TimeoutError('Frozen90seconddeadline')
def init():
    signal.signal(signal.SIGALRM,signal.SIG_DFL)
    signal.signal(signal.SIGTERM,signal.SIG_DFL)


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(90)
    start=time.monotonic()
    with mp.Pool(4,initializer=init) as pool:results=pool.map(path,[512,2048,8192,32768])
    out=dict(workers=4,seconds=time.monotonic()-start,
        source_sha256=hashlib.sha256(Path('source_screen.py').read_bytes()).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),results=results)
    Path('paths.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='results'}))
    print(json.dumps([{k:v for k,v in r.items() if k!='trajectory'} for r in results]))
