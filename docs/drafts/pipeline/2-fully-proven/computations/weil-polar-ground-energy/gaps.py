#!/usr/bin/env python3
"""Two lowest eigenvalues (gap check) of the full and pole-vanishing forms at larger apertures."""
import json
from mpmath import mp, mpf, matrix, eigsy
from weil_polar_mp import WeilMP
from multiprocessing import Pool

def run(args):
    a, N, dps = args
    mp.dps = dps
    W = WeilMP(a, N)
    A = W.arch_matrix(); P, cp, cm = W.constrained_projector()
    Pole = matrix(N, N)
    for j in range(N):
        for k in range(N):
            Pole[j, k] = cp[j] * cm[k] + cm[j] * cp[k]
    Q = A + Pole - W.prime_matrix()
    Ef = sorted(eigsy(Q, eigvals_only=True))
    Ec = sorted(eigsy(P * Q * P + mpf(1000) * (mp.eye(N) - P), eigvals_only=True))
    out = {"a": float(a), "N": N, "dps": dps,
           "full_lowest3": [mp.nstr(x, 12) for x in Ef[:3]],
           "polar_lowest3": [mp.nstr(x, 12) for x in Ec[:3]]}
    print(json.dumps(out), flush=True)
    return out

if __name__ == "__main__":
    jobs = [("0.7", 48, 60), ("0.9", 56, 60), ("1.1", 56, 80), ("1.3", 64, 80), ("1.5", 64, 100), ("2.1", 80, 140)]
    with Pool(len(jobs)) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("gaps.json", "w"), indent=1)
