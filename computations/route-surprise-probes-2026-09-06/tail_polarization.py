"""Polarized infinitesimal-tail response; no numerical limit in the cubic."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from itertools import combinations_with_replacement
from concurrent.futures import ProcessPoolExecutor
import mpmath as mp
from tail_interventions import data_with_jets
from clg_compensation import comp3


def linear_jets(x, x0, g):
    A = mp.pi*mp.exp(2*x)
    A0 = mp.pi*mp.exp(2*x0)
    e = mp.exp(-(A-A0)*g)
    return (e, -2*A*g*e, (4*A*A*g*g-4*A*g)*e,
        (-8*A**3*g**3+24*A*A*g*g-8*A*g)*e)


def run(spec):
    left, ts = spec
    mp.mp.dps = 80
    A0 = mp.pi if left=="pi" else mp.mpf(left)
    t = mp.mpf(ts)
    x0 = mp.log(A0/mp.pi)/2
    u = x0+t
    if mp.pi*mp.exp(2*u) < 6:
        return []
    gs = list(map(mp.mpf,[3,4,8,15,24,63,255]))
    atom = [data_with_jets(u,t,lambda x: linear_jets(x,x0,g)) for g in gs]
    base = data_with_jets(u,t,lambda x: (0,0,0,0))
    def p(indices):
        d = base.copy()
        for key in ("dq","da","db","dc","ds","dm","dn"):
            d[key] = sum(atom[i][key] for i in indices)
        return comp3(d,mp.mpf(0))[0]
    singles = {i:p([i]) for i in range(len(gs))}
    pairs = {(i,j):p([i,j]) for i,j in combinations_with_replacement(range(len(gs)),2)}
    rows = []
    for i,j,k in combinations_with_replacement(range(len(gs)),3):
        mixed = (p([i,j,k])-pairs[i,j]-pairs[i,k]-pairs[j,k]
            +singles[i]+singles[j]+singles[k])/6
        scale = mp.root(abs(singles[i]*singles[j]*singles[k]),3)
        rows.append(dict(left_A=left,t=ts,nodes=[str(gs[q]) for q in (i,j,k)],
            kernel=mp.nstr(mixed,30),normalized=mp.nstr(mixed/scale,30),
            diagonal=[mp.nstr(singles[q],25) for q in (i,j,k)]))
    return rows


if __name__ == "__main__":
    start = time.monotonic()
    jobs = [(a,t) for a in ("pi","4","6","9","30")
        for t in (".0001",".005",".02",".08",".2",".45",".8")]
    with ProcessPoolExecutor(max_workers=8) as pool:
        groups = list(pool.map(run,jobs))
    rows = [r for group in groups for r in group]
    neg = [r for r in rows if mp.mpf(r["kernel"])<0]
    out = dict(experiment="H4",seconds=time.monotonic()-start,dps=80,rows=rows)
    with open("polarization-results.json","w") as f:
        json.dump(out,f,indent=2)
    print("entries",len(rows),"negative",len(neg),flush=True)
    print("minimum_normalized",min(rows,key=lambda r:mp.mpf(r["normalized"])),flush=True)
    if neg:
        print("first_negative",neg[0],flush=True)
    print("seconds",out["seconds"],flush=True)
