"""Finite compressed norm savings: optimal pair partitions versus full coalition."""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import json
import time
import argparse
from concurrent.futures import ProcessPoolExecutor
import numpy as np
from scipy.linalg import eigvalsh
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csc_matrix
from weil_polar_galerkin import WeilGalerkin


def norm(a):
    eig = eigvalsh(a, check_finite=False)
    return max(abs(eig[0]), abs(eig[-1]))


def run(spec):
    a, n, control = spec
    start = time.monotonic()
    primes = [p for p in range(2, int(np.exp(2*a))+1)
        if all(p%d for d in range(2,int(np.sqrt(p))+1)) and a < np.log(p) < 2*a]
    literal = np.log(primes)
    shifts = literal if control == "literal" else np.linspace(literal[0], literal[-1], len(primes))
    weights = 2*np.log(primes)/np.sqrt(primes)
    g = WeilGalerkin(a, n)
    z = g.constrained_basis()
    matrices = [w*(z.T @ g.overlap_sym(h) @ z) for h,w in zip(shifts, weights)]
    norms = np.array([norm(m) for m in matrices])
    full = norm(sum(matrices))
    saving = float(sum(norms)-full)
    pairs = [(i,j) for i in range(len(primes)) for j in range(i+1,len(primes))]
    gains = np.array([norms[i]+norms[j]-norm(matrices[i]+matrices[j]) for i,j in pairs])
    incident = np.zeros((len(primes), len(pairs)))
    for e,(i,j) in enumerate(pairs):
        incident[i,e] = incident[j,e] = 1
    opt = milp(-gains, integrality=np.ones(len(pairs)), bounds=Bounds(0,1),
        constraints=LinearConstraint(csc_matrix(incident), 0, 1),
        options={"time_limit": 8.0, "mip_rel_gap": 1e-10})
    if opt.x is None:
        raise RuntimeError(str(opt.message))
    chosen = np.flatnonzero(opt.x > .5)
    best = float(sum(gains[chosen]))
    dual_upper = -float(opt.mip_dual_bound)
    pole_residual = max(np.max(np.abs(v @ z)) for v in g.pole_vectors())
    return dict(a=a, basis=n, control=control, primes=primes, shifts=shifts.tolist(),
        individual_sum=float(sum(norms)), full_norm=float(full), full_saving=saving,
        pairing_saving=best, pairing_upper_bound=dual_upper,
        ratio=best/saving, ratio_upper_bound=dual_upper/saving,
        matching=[[primes[pairs[e][0]],primes[pairs[e][1]]] for e in chosen],
        matching_message=opt.message, mip_gap=float(opt.mip_gap),
        pole_residual=float(pole_residual), min_pair_gain=float(min(gains)),
        seconds=time.monotonic()-start)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--basis", nargs="+", type=int, default=[24,40])
    ap.add_argument("--apertures", nargs="+", type=float, default=[1,1.4,1.8,2.2,2.6,3])
    ap.add_argument("--output", default="prime-results.json")
    args = ap.parse_args()
    start = time.monotonic()
    jobs = [(a,n,c) for a in args.apertures for n in args.basis for c in ("literal","uniform_shifts")]
    with ProcessPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(run,jobs))
    out = dict(experiment="H2",seconds=time.monotonic()-start,rows=rows)
    with open(args.output,"w") as f:
        json.dump(out,f,indent=2)
    for row in rows:
        print(row["a"],row["basis"],row["control"], "pair/full",row["ratio"],
            "upper",row["ratio_upper_bound"],"gap",row["mip_gap"],flush=True)
    print("seconds",out["seconds"],flush=True)
