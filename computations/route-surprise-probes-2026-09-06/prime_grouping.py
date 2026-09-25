"""Interaction classes: optimized small coalitions versus geometric/arithmetic groups."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from itertools import combinations
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import csc_matrix
from prime_coalitions import norm
from weil_polar_galerkin import WeilGalerkin


def run(spec):
    n,control = spec
    a = 2.2
    primes = [p for p in range(2,82) if all(p%d for d in range(2,int(p**.5)+1)) and a<np.log(p)<2*a]
    h = np.log(primes)
    if control=="uniform_shifts":
        h = np.linspace(h[0],h[-1],len(primes))
    g = WeilGalerkin(a,n)
    z = g.constrained_basis()
    matrices = [2*np.log(p)/np.sqrt(p)*(z.T@g.overlap_sym(v)@z) for p,v in zip(primes,h)]
    individual = np.array([norm(m) for m in matrices])
    total = sum(individual)
    full = norm(sum(matrices))
    saving = total-full
    groups = []
    gain = []
    for k in range(2,5):
        for group in combinations(range(len(primes)),k):
            groups.append(group)
            gain.append(float(sum(individual[list(group)])-norm(sum(matrices[i] for i in group))))
    gains = np.array(gain)
    incident = np.zeros((len(primes),len(groups)))
    for j,group in enumerate(groups):
        incident[list(group),j] = 1
    optimized = []
    for k in range(2,5):
        ix = [i for i,group in enumerate(groups) if len(group)<=k]
        result = milp(-gains[ix],integrality=np.ones(len(ix)),bounds=Bounds(0,1),
            constraints=LinearConstraint(csc_matrix(incident[:,ix]),0,1),
            options={"time_limit":12.,"mip_rel_gap":1e-8})
        if result.x is None:
            raise RuntimeError(result.message)
        chosen = [ix[i] for i,v in enumerate(result.x) if v>.5]
        optimized.append(dict(max_group=k,capture=float(sum(gains[chosen])/saving),
            capture_upper_bound=float(-result.mip_dual_bound/saving),
            gap=float(result.mip_gap),groups=[[primes[i] for i in groups[j]] for j in chosen]))
    strategies = []
    for k in (2,3,4,6,9):
        count = int(np.ceil(len(primes)/k))
        strategies += [("contiguous",k,[list(range(i,min(i+k,len(primes)))) for i in range(0,len(primes),k)]),
            ("interleaved",k,[list(range(i,len(primes),count)) for i in range(count)])]
    strategies.append(("residue_mod_6",9,[[i for i,p in enumerate(primes) if p%6==r] for r in (1,5)]))
    baseline = []
    for name,k,part in strategies:
        cost = sum(norm(sum(matrices[i] for i in group)) for group in part if group)
        baseline.append(dict(name=name,max_group=max(map(len,part)),nominal_group=k,
            capture=float((total-cost)/saving),groups=[[primes[i] for i in group] for group in part]))
    return dict(basis=n,control=control,primes=primes,full_norm=float(full),full_saving=float(saving),
        optimized=optimized,baselines=baseline)


if __name__=="__main__":
    start = time.monotonic()
    with ProcessPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(run,[(n,c) for n in (64,96) for c in ("literal","uniform_shifts")]))
    out = dict(seconds=time.monotonic()-start,rows=rows)
    with open("prime-grouping.json","w") as f:
        json.dump(out,f,indent=2)
    for r in rows:
        print(r["basis"],r["control"],"optimized",r["optimized"],flush=True)
        print("baselines",[(b["name"],b["max_group"],b["capture"]) for b in r["baselines"]],flush=True)
    print("seconds",out["seconds"],flush=True)
