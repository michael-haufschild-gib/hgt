#!/usr/bin/env python3
"""Shape of the even ground states of the restricted Weil form versus Riemann's Xi.

polar ground state G (pole-vanishing subspace): compare G(z)/((1+4z^2) G(0)) with Xi(z)/Xi(0);
full ground state H (no constraint):             compare H(z)/H(0) with Xi(z)/Xi(0).
z = t real and z = i y, 0 <= y < 1/2.  Also log-Taylor coefficient c4 = B - A^2/2
(F/F(0) = 1 + A z^2 + B z^4 + ...) and imaginary zeros of G, H on i(0, 3].
F(z) = int f(x) e^{-izx} dx, so F^(2k)(0) = (-1)^k int x^{2k} f.
"""
import sys, json
sys.path.insert(0, '/root/pbu')
from mpmath import mp, mpf, mpc, matrix, eigsy, sqrt, pi, zeta, gamma, exp, log
from weil_polar_mp import WeilMP, gl_nodes
from multiprocessing import Pool


def xi(s):
    return s * (s - 1) / 2 * pi ** (-s / 2) * gamma(s / 2) * zeta(s)


def lowest_vector(M):
    E, V = eigsy(M)
    k = min(range(len(E)), key=lambda i: E[i])
    return E[k], [V[i, k] for i in range(len(E))]


def run(args):
    a, N, dps = args
    mp.dps = dps
    W = WeilMP(a, N)
    A = W.arch_matrix()
    P, cp, cm = W.constrained_projector()
    Pole = matrix(N, N)
    for j in range(N):
        for k in range(N):
            Pole[j, k] = cp[j] * cm[k] + cm[j] * cp[k]
    Q = A + Pole - W.prime_matrix()
    eH, vH = lowest_vector(Q)
    Mc = P * Q * P + mpf(1000) * (mp.eye(N) - P)
    eG, vG = lowest_vector(Mc)
    vG = [sum(P[i, j] * vG[j] for j in range(N)) for i in range(N)]
    nodes = gl_nodes(6)   # 192 Gauss nodes on [-1,1]
    xs = [(W.a * t, W.a * w) for t, w in nodes]
    bas = [W.basis(x) for x, _ in xs]

    def tf(v):
        fv = [sum(v[j] * b[j] for j in range(N)) for b in bas]
        def F(z):
            return sum(w * f * exp(-1j * z * x) for (x, w), f in zip(xs, fv))
        def mom(k):
            return sum(w * f * x ** k for (x, w), f in zip(xs, fv))
        return F, mom

    out = {"a": a, "N": N, "dps": dps, "eH": mp.nstr(eH, 8), "eG": mp.nstr(eG, 8)}
    X0 = xi(mpf(1) / 2)
    ts = [mpf(k) / 2 for k in range(0, 41)]          # t in [0, 20]
    ys = [mpf(k) / 100 for k in range(0, 50, 4)]     # y in [0, 0.48]
    for lab, v, polar in (("G", vG, True), ("H", vH, False)):
        F, mom = tf(v)
        m0, m2, m4 = mom(0), mom(2), mom(4)
        Acoef = -m2 / (2 * m0)
        Bcoef = m4 / (24 * m0)
        c4 = Bcoef - Acoef ** 2 / 2
        F0 = F(0).real
        def R(z):
            val = F(z) / F0
            if polar:
                val = val / (1 + 4 * z * z)
            return val
        real_ratio = []
        for t in ts:
            xr = (xi(mpf(1) / 2 + 1j * t) / X0).real
            rr = R(t).real
            real_ratio.append([float(t), mp.nstr(rr, 10), mp.nstr(xr, 10),
                               mp.nstr(rr / xr if xr != 0 else mpf(0), 10)])
        imag_ratio = []
        for y in ys:
            xr = (xi(mpf(1) / 2 + y) / X0).real
            rr = R(mpc(0, y)).real
            imag_ratio.append([float(y), mp.nstr(rr, 12), mp.nstr(xr, 12)])
        imz = []
        prev = None
        for k in range(1, 601):
            y = mpf(k) / 200
            val = F(mpc(0, y)).real
            if prev is not None and prev * val < 0:
                imz.append(float(y - mpf(1) / 400))
            prev = val
        out[lab] = {"A": mp.nstr(Acoef, 12), "B": mp.nstr(Bcoef, 12), "c4": mp.nstr(c4, 12),
                    "c4_div": mp.nstr(c4 + 8, 12) if polar else None,
                    "real": real_ratio, "imag": imag_ratio, "imag_zeros": imz}
    print(json.dumps(out), flush=True)
    return out


if __name__ == "__main__":
    jobs = [(a, N, 50) for a in ("0.5", "0.6", "0.7", "0.8") for N in (40, 48)]
    with Pool(8) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("shape48.json", "w"), indent=1)
    # Xi reference Taylor data
    mp.dps = 30
    print("done")
