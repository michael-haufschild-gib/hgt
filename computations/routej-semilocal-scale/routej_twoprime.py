#!/usr/bin/env python3
"""Two-prime semilocal measure S = {p1, p2, oo}: is the residual deviation additive in the two
one-prime profiles at leading order?  Also fits the one-prime profile Phi to an envelope times sin."""
import json, math, sys
import numpy as np
from scipy.special import loggamma
from multiprocessing import Pool
from routej_scale import residual

def jacobi_radii_multi(primes, nmax, ds=0.02, extra=60.0):
    T = 2.2 * nmax + extra
    s = np.arange(-T, T + ds / 2, ds)
    logw = 2 * np.real(loggamma(0.25 + 0.5j * s))
    for p in primes:
        r = p ** -0.5; ell = math.log(p)
        logw = logw - np.log1p(r * r - 2 * r * np.cos(ell * s))
    logw -= logw.max()
    w = np.exp(np.asarray(logw, dtype=np.longdouble)) * np.longdouble(ds)
    sL = np.asarray(s, dtype=np.longdouble)
    q0 = np.sqrt(w); q0 /= np.sqrt(np.sum(q0 * q0))
    qprev = np.zeros_like(q0); qcur = q0
    a = [np.longdouble(0)]; aprev = np.longdouble(0)
    for n in range(nmax):
        t = sL * qcur - aprev * qprev
        an1 = np.sqrt(np.sum(t * t)); a.append(an1)
        qprev, qcur = qcur, t / an1; aprev = an1
    return np.array(a, dtype=np.longdouble)

def run(args):
    p1, p2, nmax = args
    a0 = jacobi_radii_multi([], nmax)
    a1 = jacobi_radii_multi([p1], nmax)
    a2 = jacobi_radii_multi([p2], nmax)
    a12 = jacobi_radii_multi([p1, p2], nmax)
    ks = list(range(1, (nmax - 6) // 2))
    R0 = np.array([residual(a0, k) for k in ks])
    D1 = np.array([residual(a1, k) for k in ks]) / R0 - 1
    D2 = np.array([residual(a2, k) for k in ks]) / R0 - 1
    D12 = np.array([residual(a12, k) for k in ks]) / R0 - 1
    nonadd = D12 - D1 - D2
    out = {"p1": p1, "p2": p2, "nmax": nmax}
    samples = []
    for k in ks:
        n = 2 * k
        if n in (20, 50, 100, 150, 200, 300, 400, 500, 600, 800, 1000, 1200):
            i = k - 1
            samples.append({"n": n, "D1": float(D1[i]), "D2": float(D2[i]), "D12": float(D12[i]),
                            "nonadd": float(nonadd[i]), "nonadd_over_sqrt(D1D2)": float(nonadd[i] / math.sqrt(abs(D1[i] * D2[i]) + 1e-300))})
    out["samples"] = samples
    out["max_abs_nonadd_n_le_p1"] = float(np.max(np.abs(nonadd[: min(len(ks), p1 // 2)])))
    out["max_abs_D12_n_le_p1"] = float(np.max(np.abs(D12[: min(len(ks), p1 // 2)])))
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    jobs = [(101, 211, 800), (307, 401, 1200), (503, 1009, 2000), (101, 1009, 2000), (211, 307, 1000)]
    with Pool(len(jobs)) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("routej_twoprime.json", "w"), indent=1)
