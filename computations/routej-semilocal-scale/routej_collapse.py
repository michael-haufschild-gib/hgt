#!/usr/bin/env python3
"""Scaling collapse test for Route J: is the relative residual deviation D_k(q) = (R_k(q)-R_k(0))/R_k(0)
a function of x = n/p = 2k q alone for large p?  Stores D at every k for large primes."""
import json, math, sys
import numpy as np
from routej_scale import jacobi_radii, residual
from multiprocessing import Pool

def run(args):
    p, nmax = args
    a = jacobi_radii(p, nmax)
    a0 = jacobi_radii(None, nmax)
    ks = list(range(1, (nmax - 6) // 2))
    D = [(residual(a, k) - residual(a0, k)) / residual(a0, k) for k in ks]
    x = [2 * k / p for k in ks]
    # first crossings of |D| >= thr in the variable x
    first = {}
    for thr in (0.05, 0.1, 0.25, 0.5, 1.0, 2.0):
        idx = [i for i, d in enumerate(D) if abs(d) >= thr]
        first[str(thr)] = (x[idx[0]] if idx else None)
    # interpolated D at fixed x
    xs = [0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.4, 1.6, 2.0]
    Dx = {}
    for xv in xs:
        k = xv * p / 2
        if k < ks[-1]:
            i = int(k) - 1
            Dx[str(xv)] = float(D[max(i, 0)])
    out = {"p": p, "nmax": nmax, "first_x": first, "D_at_x": Dx,
           "D_all": [float(d) for d in D]}
    print(json.dumps({k: v for k, v in out.items() if k != "D_all"}), flush=True)
    return out

if __name__ == "__main__":
    jobs = [(101, 800), (151, 800), (211, 1000), (307, 1200), (401, 1400), (503, 1600),
            (701, 2000), (1009, 2600), (1511, 3600), (2003, 4600)]
    with Pool(len(jobs)) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("routej_collapse.json", "w"))
