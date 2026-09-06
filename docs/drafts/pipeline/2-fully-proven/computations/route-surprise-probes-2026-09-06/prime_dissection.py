"""All coalitions at a fixed four-prime aperture, shift homotopy, parity modes."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
from functools import lru_cache
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from scipy.linalg import eigvalsh
from weil_polar_galerkin import WeilGalerkin


def norm(m):
    eig = eigvalsh(m,check_finite=False)
    return float(max(abs(eig[0]),abs(eig[-1])))


def run(spec):
    n,theta,mult = spec
    a = 1.4
    primes = [5,7,11,13]
    logs = np.log(primes)
    shifted = (1-theta)*logs+theta*np.linspace(logs[0],logs[-1],4)
    g = WeilGalerkin(a,n,Mx=mult*(n+8))
    raw = [2*np.log(p)/np.sqrt(p)*g.overlap_sym(h) for p,h in zip(primes,shifted)]
    cp,cm = g.pole_vectors()
    spaces = {"unconstrained":np.eye(n),"constrained":g.constrained_basis()}
    for name,parity in (("even",0),("odd",1)):
        ix = np.arange(parity,n,2)
        _,_,v = np.linalg.svd(cp[ix].reshape(1,-1))
        spaces[name] = np.eye(n)[:,ix]@v[1:].T
    rows = []
    for name,z in spaces.items():
        matrices = [z.T @ m @ z for m in raw]
        norms = {mask:norm(sum(matrices[i] for i in range(4) if mask&(1<<i)))
            for mask in range(1,16)}
        total = sum(norms[1<<i] for i in range(4))
        saving = total-norms[15]
        def optimal(k):
            @lru_cache(None)
            def dp(mask):
                if mask==0:
                    return (0,())
                anchor = mask & -mask
                sub = mask
                best = (float("inf"),())
                while sub:
                    if sub&anchor and bin(sub).count("1")<=k:
                        cost,part = dp(mask^sub)
                        if norms[sub]+cost < best[0]:
                            best = (norms[sub]+cost,(sub,)+part)
                    sub = (sub-1)&mask
                return best
            cost,part = dp(15)
            return dict(max_size=k,saving=total-cost,capture=(total-cost)/saving,
                groups=[[primes[i] for i in range(4) if m&(1<<i)] for m in part])
        eig,vec = np.linalg.eigh(sum(matrices))
        idx = int(np.argmax(abs(eig)))
        grid = np.linspace(-a,a,201)
        profile = g.basis(grid) @ z @ vec[:,idx]
        rows.append(dict(basis=n,theta=theta,quadrature_multiplier=mult,space=name,
            shifts=shifted.tolist(),individual_sum=total,full_norm=norms[15],
            full_saving=saving,partitions=[optimal(k) for k in range(1,5)],
            dominant_eigenvalue=float(eig[idx]),top_algebraic=eig[-3:].tolist(),
            bottom_algebraic=eig[:3].tolist(),norms={str(k):v for k,v in norms.items()},
            profile_grid=grid.tolist(),profile=profile.tolist()))
    return rows


if __name__ == "__main__":
    start = time.monotonic()
    jobs = [(n,float(t),1) for n in (40,96) for t in np.linspace(0,1,21)]
    jobs += [(96,t,2) for t in (0.,.5,1.)]
    with ProcessPoolExecutor(max_workers=8) as pool:
        groups = list(pool.map(run,jobs))
    rows = [r for g in groups for r in g]
    out = dict(seconds=time.monotonic()-start,rows=rows)
    with open("prime-dissection.json","w") as f:
        json.dump(out,f,indent=2)
    for r in rows:
        if r["theta"] in (0.,.5,1.) and r["quadrature_multiplier"]==1:
            print(r["basis"],r["theta"],r["space"],"full",r["full_norm"],
                "capture",[round(p["capture"],5) for p in r["partitions"]],flush=True)
    print("seconds",out["seconds"],flush=True)
