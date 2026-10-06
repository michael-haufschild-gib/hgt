#!/usr/bin/env python3
"""Aperture dependence of the real zeros of the restricted-Weil ground states.
For a on a fine grid in [0.30, 0.80] (Galerkin converged range), compute the unconstrained (H) and
polar (G) ground states (Legendre N=40, mpmath 50 digits, quadrature exact for N<=48) and their first
real transform zeros on (0, 60]. Question: is every zero x_k(a) non-increasing in a, also across the
prime-power entries a = (log n)/2?"""
import sys, json
sys.path.insert(0, '/root/pbu')
from mpmath import mp, mpf, matrix, eigsy, findroot
from weil_polar_mp import WeilMP, gl_nodes
from multiprocessing import Pool


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
    nodes = gl_nodes(6)
    xs = [(W.a * t, W.a * w) for t, w in nodes]
    bas = [W.basis(x) for x, _ in xs]
    out = {"a": a, "N": N, "eH": mp.nstr(eH, 8), "eG": mp.nstr(eG, 8)}
    for lab, v in (("H", vH), ("G", vG)):
        fv = [sum(v[j] * b[j] for j in range(N)) for b in bas]
        even = sum(v[j] ** 2 for j in range(0, N, 2)) > sum(v[j] ** 2 for j in range(1, N, 2))
        def F(t):
            if even:
                return sum(w * f * mp.cos(t * x) for (x, w), f in zip(xs, fv))
            return sum(w * f * mp.sin(t * x) for (x, w), f in zip(xs, fv))
        zs = []
        step = mpf('0.05')
        t = step
        prev = F(t)
        while t < 56:
            t2 = t + step
            cur = F(t2)
            if prev * cur < 0:
                zs.append(float(findroot(F, (t, t2), solver='bisect', tol=mpf(10) ** (-20))))
            prev, t = cur, t2
        out[lab] = {"even": bool(even), "zeros": zs}
    print(json.dumps(out), flush=True)
    return out


if __name__ == "__main__":
    grid = ["0.775", "0.800", "0.825", "0.850"]
    jobs = [(a, N, 60) for a in grid for N in (40, 48)]
    with Pool(8) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("mono_hi.json", "w"), indent=1)
