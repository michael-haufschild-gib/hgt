#!/usr/bin/env python3
"""Is the one-prime profile Phi the FIRST-ORDER response to the Fourier mode cos(s log p)?
First-order perturbation of the Jacobi radii under the multiplier 1 + 2 eps cos(delta s) (in the
orthonormal basis the Gram matrix is I + eps B with B_ij = 2 <p_i, cos(delta s) p_j>):
   a_n(eps)^2 = a_n^2 (1 + eps (D_{n-1} + D_{n+1} - 2 D_n)) + O(eps^2),  D_n = tr B_{<=n} = 2 sum_{j<=n} m_j,
   m_j = <p_j^2, cos(delta s)>,   so  a_n(eps) = a_n (1 + eps (m_{n+1} - m_n)) + O(eps^2)   [code index a[n] <-> p_{n-1},p_n]
For one prime: the Euler factor = sum_d r^{|d|}/(1-r^2) e^{i d ell s}, so the cos(ell s) amplitude is eps_1 = r/(1-r^2) with r = p^{-1/2},
the cos(2 ell s) amplitude eps_2 = r^2/(1-r^2), etc.  We compare the exact D with the first-order-in-eps_1 prediction and with
the sum of first-order responses of all harmonics d = 1..4."""
import json, math
import numpy as np
from scipy.special import loggamma
from multiprocessing import Pool
from routej_scale import residual

def stieltjes_with_modes(nmax, freqs, ds=0.02, extra=60.0, prime=None):
    T = 2.2 * nmax + extra
    s = np.arange(-T, T + ds / 2, ds)
    logw = 2 * np.real(loggamma(0.25 + 0.5j * s))
    if prime is not None:
        r = prime ** -0.5; ell = math.log(prime)
        logw = logw - np.log1p(r * r - 2 * r * np.cos(ell * s))
    logw -= logw.max()
    w = np.exp(np.asarray(logw, dtype=np.longdouble)) * np.longdouble(ds)
    sL = np.asarray(s, dtype=np.longdouble)
    cosines = [np.asarray(np.cos(f * s), dtype=np.longdouble) for f in freqs]
    q0 = np.sqrt(w); q0 /= np.sqrt(np.sum(q0 * q0))
    qprev = np.zeros_like(q0); qcur = q0
    a = [np.longdouble(0)]; aprev = np.longdouble(0)
    m = [[float(np.sum(q0 * q0 * c))] for c in cosines]        # m_0 for each frequency
    for n in range(nmax):
        t = sL * qcur - aprev * qprev
        an1 = np.sqrt(np.sum(t * t)); a.append(an1)
        qprev, qcur = qcur, t / an1; aprev = an1
        for i, c in enumerate(cosines):
            m[i].append(float(np.sum(qcur * qcur * c)))
    return np.array(a, dtype=np.longdouble), [np.array(mi) for mi in m]

def run(p):
    nmax = int(2.6 * p) + 40
    r = p ** -0.5; ell = math.log(p)
    a0, ms = stieltjes_with_modes(nmax, [d * ell for d in (1, 2, 3, 4)])
    aex, _ = stieltjes_with_modes(nmax, [], prime=p)
    eps = [r ** d / (1 - r * r) for d in (1, 2, 3, 4)]
    # first-order radii: a[n] <-> p_{n-1}, p_n ; jet: a[n](1 + eps (m_n - m_{n-1}))  (m indexed by polynomial degree)
    def first_order(dlist):
        af = np.array(a0, dtype=np.float64).copy()
        for n in range(1, nmax + 1):
            corr = sum(eps[d - 1] * (ms[d - 1][n] - ms[d - 1][n - 1]) for d in dlist)
            af[n] = float(a0[n]) * (1 + corr)
        return af
    a1 = first_order([1]); a14 = first_order([1, 2, 3, 4])
    ks = list(range(1, (nmax - 6) // 2))
    R0 = np.array([residual(a0, k) for k in ks])
    Dex = np.array([residual(aex, k) for k in ks]) / R0 - 1
    D1 = np.array([residual(a1, k) for k in ks]) / R0 - 1
    D14 = np.array([residual(a14, k) for k in ks]) / R0 - 1
    out = {"p": p, "nmax": nmax}
    out["samples"] = [{"x": 2 * k / p, "D_exact": float(Dex[k - 1]), "D_first_order_d1": float(D1[k - 1]), "D_first_order_d1to4": float(D14[k - 1]),
                       "m1_n": float(ms[0][2 * k]), "sqrtp_m1": float(math.sqrt(p) * ms[0][2 * k])}
                      for k in ks if abs(2 * k / p - round(2 * k / p * 10) / 10) < 1e-9 or (2 * k) % 100 == 0]
    out["corr_exact_first"] = float(np.corrcoef(Dex, D1)[0, 1])
    out["rms_ratio_first_over_exact"] = float(math.sqrt(np.mean(D1 ** 2) / np.mean(Dex ** 2)))
    print(json.dumps({k: v for k, v in out.items() if k != "samples"}), flush=True)
    return out

if __name__ == "__main__":
    with Pool(4) as pool:
        res = pool.map(run, [211, 503, 1009, 1511])
    json.dump(res, open("routej_firstorder.json", "w"), indent=1)
