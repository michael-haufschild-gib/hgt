#!/usr/bin/env python3
"""Cross-prime term of the two-prime semilocal Jacobi residual.
(a) pairs with (nearly) the same ratio p2/p1: does nonadd*sqrt(p1 p2) collapse as a function of n?
(b) synthetic measure: archimedean weight times (1 + 2 eps cos(delta s)), eps = (p1 p2)^{-1/2},
    delta = log(p2/p1): does it reproduce the non-additive part?"""
import json, math
import numpy as np
from scipy.special import loggamma
from multiprocessing import Pool
from routej_scale import residual

def radii(nmax, primes=(), synthetic=None, ds=0.02, extra=60.0):
    T = 2.2 * nmax + extra
    s = np.arange(-T, T + ds / 2, ds)
    logw = 2 * np.real(loggamma(0.25 + 0.5j * s))
    for p in primes:
        r = p ** -0.5; ell = math.log(p)
        logw = logw - np.log1p(r * r - 2 * r * np.cos(ell * s))
    if synthetic is not None:
        eps, delta = synthetic
        logw = logw + np.log(1 + 2 * eps * np.cos(delta * s))
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
    a0 = radii(nmax); a1 = radii(nmax, (p1,)); a2 = radii(nmax, (p2,)); a12 = radii(nmax, (p1, p2))
    eps = (p1 * p2) ** -0.5; delta = math.log(p2 / p1)
    asyn = radii(nmax, synthetic=(eps, delta))
    ks = list(range(1, (nmax - 6) // 2))
    R0 = np.array([residual(a0, k) for k in ks])
    D1 = np.array([residual(a1, k) for k in ks]) / R0 - 1
    D2 = np.array([residual(a2, k) for k in ks]) / R0 - 1
    D12 = np.array([residual(a12, k) for k in ks]) / R0 - 1
    Dsyn = np.array([residual(asyn, k) for k in ks]) / R0 - 1
    nonadd = D12 - D1 - D2
    out = {"p1": p1, "p2": p2, "eps": eps, "delta": delta, "nmax": nmax,
           "corr_nonadd_syn": float(np.corrcoef(nonadd, Dsyn)[0, 1]),
           "ratio_rms": float(np.sqrt(np.mean(nonadd ** 2) / np.mean(Dsyn ** 2)))}
    out["samples"] = [{"n": 2 * k, "nonadd": float(nonadd[k - 1]), "Dsyn": float(Dsyn[k - 1]),
                       "scaled": float(nonadd[k - 1] / eps)} for k in ks if 2 * k in (20, 40, 60, 100, 150, 200, 300, 400, 600, 800)]
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    jobs = [(101, 211, 900), (211, 421, 900), (503, 1009, 900), (1009, 2017, 900), (307, 401, 900), (997, 1009, 900)]
    with Pool(len(jobs)) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("routej_crossterm.json", "w"), indent=1)
