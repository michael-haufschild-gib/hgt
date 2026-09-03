#!/usr/bin/env python3
"""Bisection (double precision, N = 64) for the apertures where the pole-vanishing ground energy
of truncated forms changes sign: archimedean only, primes <= 2, primes <= 3."""
import json, math
import numpy as np
from weil_polar_galerkin import WeilGalerkin

def mu0(a, N, pmax, arch_only=False):
    W = WeilGalerkin(a, N)
    A = W.arch_matrix()
    Z = W.constrained_basis()
    Q = A if arch_only else A - W.prime_matrix(pmax=pmax)
    return W.lowest(Z.T @ Q @ Z)[0]

def bisect(f, lo, hi, tol=2e-6):
    flo, fhi = f(lo), f(hi)
    assert flo > 0 > fhi, (flo, fhi)
    while hi - lo > tol:
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return lo, hi

out = {}
for label, kw, lo, hi in (("arch_only", dict(pmax=None, arch_only=True), 0.58, 0.61),
                          ("primes_le_2", dict(pmax=2), 0.55, 0.58),
                          ("primes_le_3", dict(pmax=3), 0.69, 0.72)):
    res = {}
    for N in (48, 64, 80):
        l, h = bisect(lambda a: mu0(a, N, **kw), lo, hi)
        res[str(N)] = {"a_lo": l, "a_hi": h, "lambda": math.exp(0.5 * (l + h)), "S": l + h}
        print(label, N, res[str(N)], flush=True)
    out[label] = res
out["entries"] = {"log2/2": math.log(2) / 2, "log3/2": math.log(3) / 2, "log4/2": math.log(4) / 2,
                  "log5/2": math.log(5) / 2}
json.dump(out, open("thresholds.json", "w"), indent=1)
print(json.dumps(out["entries"]))
