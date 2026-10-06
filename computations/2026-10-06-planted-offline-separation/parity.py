#!/usr/bin/env python3
"""Even/odd sector ground energies of the restricted Weil form, true and with a planted off-line quartet
+-g1 +- i d replacing +-g1 (explicit-formula substitution).  One matrix assembly per aperture; all
planted variants derived from it.  Questions: (i) do both sectors cross zero at the same aperture
(first contact)? (ii) does mu_even - mu_odd change sign after contact (forced parity crossings)?"""
import sys, json
sys.path.insert(0, '/root/pbu')
from mpmath import mp, mpf, mpc, matrix, eigsy, exp
from weil_polar_mp import WeilMP, gl_nodes
from multiprocessing import Pool

G1 = mpf('14.134725141734693790457251983562')

def sub(M, idx):
    S = matrix(len(idx), len(idx))
    for i, a in enumerate(idx):
        for j, b in enumerate(idx):
            S[i, j] = M[a, b]
    return S

def lowest(M):
    return min(eigsy(M, eigvals_only=True))

def run(a):
    N, dps = 40, 50
    mp.dps = dps
    W = WeilMP(a, N)
    A = W.arch_matrix()
    _, cp, cm = W.constrained_projector()
    Pole = matrix(N, N)
    for j in range(N):
        for k in range(N):
            Pole[j, k] = cp[j] * cm[k] + cm[j] * cp[k]
    Q = A + Pole - W.prime_matrix()
    nodes = gl_nodes(6)
    xs = [(W.a * t, W.a * w) for t, w in nodes]
    bas = [W.basis(x) for x, _ in xs]
    def btrans(z):
        return [sum(w * b[j] * exp(-1j * z * x) for (x, w), b in zip(xs, bas)) for j in range(N)]
    def contrib(z):
        bz = btrans(z); bzc = btrans(z.conjugate())
        M = matrix(N, N)
        for j in range(N):
            for k in range(N):
                M[j, k] = ((bz[j] * bzc[k].conjugate()) + (bz[k] * bzc[j].conjugate())).real / 2
        return M
    base = contrib(mpc(G1, 0)) + contrib(mpc(-G1, 0))
    ev = list(range(0, N, 2)); od = list(range(1, N, 2))
    out = {"a": a, "true": {"even": mp.nstr(lowest(sub(Q, ev)), 10), "odd": mp.nstr(lowest(sub(Q, od)), 10)}}
    for d in ("0.05", "0.15", "0.30"):
        dd = mpf(d)
        corr = -base
        for s in (1, -1):
            for e in (1, -1):
                corr += contrib(mpc(s * G1, e * dd))
        Qp = Q + corr
        out[d] = {"even": mp.nstr(lowest(sub(Qp, ev)), 10), "odd": mp.nstr(lowest(sub(Qp, od)), 10)}
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    grid = [f"{0.40 + 0.015 * i:.3f}" for i in range(24)]
    with Pool(8) as pool:
        res = pool.map(run, grid)
    json.dump(res, open("parity.json", "w"), indent=1)
