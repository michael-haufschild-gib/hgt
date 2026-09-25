"""Balanced random partition null control for the proposed arithmetic grouping."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from prime_coalitions import norm
from weil_polar_galerkin import WeilGalerkin


def run(spec):
    n,control = spec
    a = 2.2
    primes = [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79]
    h = np.log(primes)
    if control=="uniform_shifts":
        h = np.linspace(h[0],h[-1],len(primes))
    g = WeilGalerkin(a,n,Mx=2*(n+8))
    z = g.constrained_basis()
    matrices = np.array([2*np.log(p)/np.sqrt(p)*(z.T@g.overlap_sym(v)@z) for p,v in zip(primes,h)])
    norms = np.array([norm(m) for m in matrices])
    total_matrix = sum(matrices)
    full = norm(total_matrix)
    saving = sum(norms)-full
    rng = np.random.default_rng(20260906)
    subsets = [np.flatnonzero(np.array(primes)%6==1)]
    subsets += [rng.choice(18,9,replace=False) for _ in range(512)]
    values = []
    for subset in subsets:
        a_matrix = sum(matrices[subset])
        cost = norm(a_matrix)+norm(total_matrix-a_matrix)
        values.append(dict(capture=float((sum(norms)-cost)/saving),
            norm_mass_imbalance=float(abs(2*sum(norms[subset])-sum(norms))/sum(norms)),
            group=[primes[i] for i in sorted(subset)]))
    null = [r["capture"] for r in values[1:]]
    return dict(basis=n,control=control,doubled_quadrature=True,residue=values[0],
        random_quantiles=np.quantile(null,[0,.05,.25,.5,.75,.95,1]).tolist(),
        residue_empirical_percentile=float(np.mean(np.array(null)<=values[0]["capture"])),
        rows=values[1:])


if __name__=="__main__":
    start = time.monotonic()
    with ProcessPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(run,[(n,c) for n in (64,96) for c in ("literal","uniform_shifts")]))
    out = dict(seconds=time.monotonic()-start,rows=rows)
    with open("prime-partition-controls.json","w") as f:
        json.dump(out,f,indent=2)
    for r in rows:
        print({k:v for k,v in r.items() if k!="rows"},flush=True)
    print("seconds",out["seconds"],flush=True)
