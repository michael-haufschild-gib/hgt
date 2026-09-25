"""Runpod-only exploration of arithmetic remainder minimum classes."""
import os
for key in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import concurrent.futures
import json
import math
import platform
import time
import mpmath as mp
import numpy as np
import scipy
from scipy.special import zeta as hzeta

MAX_P = 256
WORKERS = 8


def mobius_table(limit):
    mu = np.ones(limit + 1, dtype=np.int64)
    prime = np.ones(limit + 1, dtype=bool)
    for p in range(2, limit + 1):
        if prime[p]:
            mu[p::p] *= -1
            mu[p*p::p*p] = 0
            prime[p*2::p] = False
    mu[0] = 0
    return mu


def values(s, zs, head_factor, order):
    sigma, height = s.real, s.imag
    top = int(math.ceil(head_factor * abs(height))) + 512
    integers = np.arange(1, top + 1, dtype=np.float64)
    logs = np.log(integers)
    kernels = np.exp(-s * logs)
    sums = np.cumsum(kernels)
    remainder = sums - zs - np.exp((1-s)*logs)/(1-s) - kernels/2
    p = np.arange(1, MAX_P + 1, dtype=np.float64)
    heads = top // p.astype(np.int64)
    w = np.empty(MAX_P, dtype=np.complex128)
    for pi in range(1, MAX_P + 1):
        n = np.arange(1, int(heads[pi-1]) + 1)
        w[pi-1] = np.exp((1-s)*np.log(pi)) * np.sum(
            kernels[n-1] * np.conj(remainder[pi*n-1]))
    u = s.conjugate()
    for k in range(1, order + 1):
        rising = complex(1)
        for j in range(2*k-1):
            rising *= u+j
        coefficient = -float(mp.bernoulli(2*k))/math.factorial(2*k)*rising
        w += coefficient * p**(2-2*sigma-2*k) * hzeta(2*sigma+2*k-1, heads+1.0)
    return w


def task(index):
    mp.mp.dps = 45
    zero = mp.zetazero(index)
    height = float(mp.im(zero))
    rows = []
    sigmas = [0.5] + ([0.4, 0.6, 0.8] if index <= 16 else [])
    p = np.arange(1, MAX_P + 1, dtype=float)
    mu = mobius_table(MAX_P)[1:]
    for sigma in sigmas:
        smp = mp.mpc(str(sigma), mp.im(zero))
        s = complex(smp)
        zs = complex(mp.zeta(smp))
        wa = values(s, zs, 6, 10)
        wb = values(s, zs, 9, 14)
        base = (mu * wb / (s.conjugate()*(s.conjugate()+1))).real
        x = p * base
        y = p**(4*sigma-1) * base
        c = float(mp.zeta(2*sigma+1)/12 * mp.re(1/(mp.conj(smp)+1)))
        imin = int(np.argmin(x))
        row = {"zero_index": index, "sigma": sigma, "height": str(mp.im(zero)),
               "zeta": [zs.real, zs.imag], "min_X_index": imin+1,
               "min_X": float(x[imin]), "wall_tail_lower_boundary": -c,
               "min_X_minus_wall_boundary": float(x[imin]+c),
               "head_order_max_W_drift": float(np.max(np.abs(wb-wa))),
               "head_order_max_X_drift": float(np.max(np.abs(
                   p*(mu*(wb-wa)/(s.conjugate()*(s.conjugate()+1))).real))),
               "rows": [[i+1, int(mu[i]), float(wb[i].real), float(wb[i].imag),
                         float(x[i]), float(y[i])] for i in range(MAX_P)]}
        rows.append(row)
    print("zero", index, "min p", rows[0]["min_X_index"],
          "gap", rows[0]["min_X_minus_wall_boundary"], flush=True)
    return rows


if __name__ == "__main__":
    start = time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=WORKERS) as pool:
        groups = list(pool.map(task, range(1, 97)))
    data = {"note": "Exploration only; approximations and asymptotic tails are not proof certificates.",
            "python": platform.python_version(), "numpy": np.__version__,
            "scipy": scipy.__version__, "mpmath": mp.__version__, "digits": 45,
            "workers": WORKERS, "max_p": MAX_P, "head_factors": [6, 9],
            "orders": [10, 14], "seconds": time.time()-start,
            "columns": ["p", "mu", "Re W", "Im W", "X", "Y"],
            "results": [row for group in groups for row in group]}
    with open("results.json", "w") as out:
        json.dump(data, out, indent=2)
