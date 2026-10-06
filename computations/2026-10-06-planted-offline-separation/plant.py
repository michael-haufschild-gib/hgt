#!/usr/bin/env python3
"""Planted off-line zero in the actual restricted Weil form.  Q(f) = sum_rho F(gamma)F^#(gamma) (explicit
formula).  Planted form: Q'(f) = Q(f) - [contribution of the on-line pair +-g1] + [contribution of the
quartet +-g1 +- i d], with g1 = 14.1347...; for real coefficient vectors and even/odd bases the
contribution of a point z is F(z) * conj(F(conj z)).  Track ground energy sign (first contact) and the
nested-aperture separation of ground-state real zeros, before and after contact."""
import sys, json
sys.path.insert(0, '/root/pbu')
from mpmath import mp, mpf, mpc, matrix, eigsy, findroot, exp, cos, sin
from weil_polar_mp import WeilMP, gl_nodes
from multiprocessing import Pool

G1 = mpf('14.134725141734693790457251983562')

def run(args):
    a, d, N, dps = args
    mp.dps = dps
    d = mpf(d)
    W = WeilMP(a, N)
    A = W.arch_matrix()
    P, cp, cm = W.constrained_projector()
    Pole = matrix(N, N)
    for j in range(N):
        for k in range(N):
            Pole[j, k] = cp[j] * cm[k] + cm[j] * cp[k]
    Q = A + Pole - W.prime_matrix()
    nodes = gl_nodes(6)
    xs = [(W.a * t, W.a * w) for t, w in nodes]
    bas = [W.basis(x) for x, _ in xs]
    def btrans(z):  # basis transforms F_j(z) = int b_j(x) e^{-izx} dx
        return [sum(w * b[j] * exp(-1j * z * x) for (x, w), b in zip(xs, bas)) for j in range(N)]
    def contrib(z):  # matrix of F(z) conj F(conj z) as a real symmetric form on real coefficient vectors
        bz = btrans(z); bzc = btrans(z.conjugate())
        M = matrix(N, N)
        for j in range(N):
            for k in range(N):
                v = bz[j] * bzc[k].conjugate()
                M[j, k] = (v + (bz[k] * bzc[j].conjugate())).real / 2
        return M
    corr = matrix(N, N)
    for s in (1, -1):
        corr -= contrib(mpc(s * G1, 0))
        for e in (1, -1):
            corr += contrib(mpc(s * G1, e * d))
    Qp = Q + corr
    E, V = eigsy(Qp)
    k0 = min(range(N), key=lambda i: E[i])
    v = [V[i, k0] for i in range(N)]
    even = sum(v[j] ** 2 for j in range(0, N, 2)) > sum(v[j] ** 2 for j in range(1, N, 2))
    fv = [sum(v[j] * b[j] for j in range(N)) for b in bas]
    def F(t):
        if even:
            return sum(w * f * cos(t * x) for (x, w), f in zip(xs, fv))
        return sum(w * f * sin(t * x) for (x, w), f in zip(xs, fv))
    zs = []; step = mpf('0.05'); t = step; prev = F(t)
    while t < 40:
        t2 = t + step; cur = F(t2)
        if prev * cur < 0:
            zs.append(float(findroot(F, (t, t2), solver='bisect', tol=mpf(10) ** (-20))))
        prev, t = cur, t2
    out = {"a": a, "d": float(d), "N": N, "energy": mp.nstr(E[k0], 10), "even": bool(even), "zeros": zs}
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    grid = [f"{0.30 + 0.05 * i:.2f}" for i in range(11)]
    jobs = [(a, d, 40, 50) for d in ("0.05", "0.15", "0.3") for a in grid]
    with Pool(8) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("plant.json", "w"), indent=1)
