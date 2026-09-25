#!/usr/bin/env python3
"""
Route J (semilocal one-prime Jacobi matrix): at which degree does the Euler deformation become
order one?

Measure (Connes--Consani--Moscovici, S = {p, oo}):
    d nu_p(s) = |Gamma(1/4 + i s/2)|^2 * |1 - p^{-1/2} e^{i s log p}|^{-2} ds / normalization,
q = 1/p.  Orthonormal polynomials p_n with  s p_n = a_{n+1} p_{n+1} + a_n p_{n-1}  (symmetric
measure, no diagonal).  At q = 0 the corpus's archimedean radii are r_n = sqrt((n+1/2)(n+1)) (index
convention checked below).  Route J's four-radius critical residual:
    R_k(q) = a_{2k} a_{2k+1} - a_{2k+1}^2 - a_{2k+2}^2 + a_{2k+2} a_{2k+3}.

Method: discretized Stieltjes procedure on a fine grid, run on the normalized functions
q_n(s) = p_n(s) sqrt(w(s)) so that everything stays O(1) (double precision suffices).
Validation: q = 0 radii against sqrt((n+1/2)(n+1)); grid-refinement stability.
"""
import json, math, sys
import numpy as np
from scipy.special import loggamma
from multiprocessing import Pool


def jacobi_radii(p, nmax, ds=0.02, extra=60.0):
    """Off-diagonal recurrence coefficients a_1..a_nmax of d nu_p (p=None: archimedean)."""
    T = 2.2 * nmax + extra
    s = np.arange(-T, T + ds / 2, ds)
    logw = 2 * np.real(loggamma(0.25 + 0.5j * s))
    if p is not None:
        r = p ** -0.5
        ell = math.log(p)
        logw = logw - np.log1p(r * r - 2 * r * np.cos(ell * s))     # |1 - r e^{i ell s}|^{-2}
    logw -= logw.max()
    # extended precision (80-bit long double, exponent range 1e+-4932) so that the weight does not
    # underflow on the support of the high-degree orthonormal functions
    w = np.exp(np.asarray(logw, dtype=np.longdouble)) * np.longdouble(ds)
    sL = np.asarray(s, dtype=np.longdouble)
    q0 = np.sqrt(w)
    q0 /= np.sqrt(np.sum(q0 * q0))
    qprev = np.zeros_like(q0)
    qcur = q0
    a = [np.longdouble(0)]
    aprev = np.longdouble(0)
    for n in range(nmax):
        t = sL * qcur - aprev * qprev            # = a_{n+1} q_{n+1}   (symmetric measure: b_n = 0)
        an1 = np.sqrt(np.sum(t * t))
        a.append(an1)
        qprev, qcur = qcur, t / an1
        aprev = an1
    return np.array(a, dtype=np.longdouble)   # a[n] = a_n for n >= 1  (corpus radius r_{n-1})


def residual(a, k):
    """Corpus residual R_k = A_{2k}A_{2k+1} - A_{2k+1}^2 - A_{2k+2}^2 + A_{2k+2}A_{2k+3} with the corpus
    radius A_n = a[n+1] (a[n] is the coefficient linking p_{n-1} and p_n)."""
    A = lambda n: a[n + 1]
    return float(A(2 * k) * A(2 * k + 1) - A(2 * k + 1) ** 2 - A(2 * k + 2) ** 2 + A(2 * k + 2) * A(2 * k + 3))


def run(p):
    nmax = 1400
    a = jacobi_radii(p, nmax)
    a0 = jacobi_radii(None, nmax)
    out = {"p": p, "q": 1.0 / p, "nmax": nmax}
    ks = list(range(1, (nmax - 6) // 2))
    R = np.array([residual(a, k) for k in ks])
    R0 = np.array([residual(a0, k) for k in ks])
    D = (R - R0) / R0
    out["R0_tail"] = float(R0[-1])
    first = {}
    for thr in (0.01, 0.05, 0.1, 0.25, 0.5, 1.0):
        idx = np.where(np.abs(D) >= thr)[0]
        first[str(thr)] = int(ks[idx[0]]) if len(idx) else None
    out["first_k_abs_dev_ge"] = first
    # scaled slopes: (R_k(q) - R_k(0)) / (q sqrt(2k))  and  vs the corpus first-jet law 4 sqrt(2/pi) sqrt(2(2k+2))
    sl = [(int(k), float((R[i] - R0[i]) / (1.0 / p))) for i, k in enumerate(ks) if k in (1, 2, 5, 10, 20, 50, 100, 200, 400, 600)]
    out["slope_dR_dq"] = sl
    out["D_samples"] = [(int(k), float(D[i])) for i, k in enumerate(ks) if k in (1, 2, 3, 5, 8, 12, 20, 30, 50, 80, 120, 200, 300, 450, 600, 690)]
    out["a_samples"] = [(int(n), float(a[n]), float(a0[n]), math.sqrt((n - 0.5) * n)) for n in (1, 2, 3, 4, 10, 50, 200, 800, 1400)]
    print(json.dumps(out), flush=True)
    return out


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"
    if mode == "check":
        a0 = jacobi_radii(None, 60)
        r = [math.sqrt((n + 0.5) * (n + 1)) for n in range(0, 61)]
        print("archimedean a_n vs r_{n-1} = sqrt((n-1/2) n):", [(n, round(a0[n], 8), round(math.sqrt((n - 0.5) * n), 8)) for n in (1, 2, 3, 10, 30, 60)])
        print("archimedean a_n vs r_n = sqrt((n+1/2)(n+1)):", [(n, round(a0[n], 8), round(r[n], 8)) for n in (1, 2, 3, 10, 30, 60)])
        a0b = jacobi_radii(None, 60, ds=0.01)
        print("grid refinement max |diff|:", float(np.max(np.abs(a0 - a0b))))
        a2 = jacobi_radii(2, 60)
        a2b = jacobi_radii(2, 60, ds=0.01, extra=120.0)
        print("p=2 grid refinement max |diff|:", float(np.max(np.abs(a2 - a2b))))
        print("p=2 a_n:", [(n, round(a2[n], 8)) for n in (1, 2, 3, 4, 5, 10)])
        print("R_k(0) for k=1..6, 300, 600:", [round(residual(a0, k), 8) for k in (1, 2, 3, 4, 5, 6)])
        a0L = jacobi_radii(None, 1300)
        for n in (300, 600, 1000, 1300):
            print("drift n=%d: %.3e" % (n, float(a0L[n]) - math.sqrt((n - 0.5) * n)))
        print("R_k(0) k=300,600:", residual(a0L, 300), residual(a0L, 600))
    else:
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 41, 53, 71, 101, 151, 211, 307, 401, 503, 701, 1009]
        with Pool(min(16, len(primes))) as pool:
            res = pool.map(run, primes)
        json.dump(res, open("routej_scale.json", "w"), indent=1)
