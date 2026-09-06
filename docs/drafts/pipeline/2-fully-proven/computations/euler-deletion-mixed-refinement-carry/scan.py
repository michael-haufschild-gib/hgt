"""Runpod-only exploratory evaluation; outputs are not proof certificates."""
import os

for _name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_name] = "1"

import argparse
import concurrent.futures
import json
import math
import platform
import time

import mpmath as mp
import numpy as np

BASES = (2, 3, 5, 7, 11)
PAIRS = tuple((p, q) for p in BASES for q in BASES if p != q)
CUTOFFS = (36960, 147840, 591360)


def packed(z):
    return [float(z.real), float(z.imag)]


def task(spec):
    start = time.time()
    mp.mp.dps = 70
    if "zero" in spec:
        height = mp.im(mp.zetazero(spec["zero"]))
    else:
        height = mp.mpf(spec["height"])
    s_mp = mp.mpc(mp.mpf(spec["sigma"]), height)
    s = complex(s_mp)
    zeta = complex(mp.zeta(s_mp))
    nmax = CUTOFFS[-1]
    k = np.arange(nmax, dtype=np.int64)
    n = k + 1
    u = np.exp(-s * np.log(n.astype(np.float64)))
    sums = np.empty(nmax + 1, dtype=np.complex128)
    sums[0] = 0
    np.cumsum(u, out=sums[1:])
    mods = sorted(set(BASES) | {p * q for p, q in PAIRS})
    tails = {}
    mixed = {}
    endpoints = {}
    for p in mods:
        c = complex(mp.power(p, 1 - s_mp))
        dp = (1 - c) * zeta
        tail = sums[k] - c * sums[k // p] - dp
        primitive = np.cumsum(tail * np.conj(u))
        mixed[str(p)] = [packed(primitive[N - 1]) for N in CUTOFFS]
        endpoints[str(p)] = [
            packed(sums[N] - c * sums[N // p] - dp) for N in CUTOFFS
        ]
        if p in BASES:
            tails[p] = tail
    correction = {}
    identity_error = {}
    for p in BASES:
        c = complex(mp.power(p, 1 - s_mp))
        last_weight = np.exp(-s.conjugate() * (math.log(p) + np.log(n)))
        cell_variation = np.zeros(nmax, dtype=np.complex128)
        # Stable evaluation of sum_r w(pk+r)-p*w(pk+p).
        for r in range(1, p):
            cell_variation += np.expm1(
                -s.conjugate() * np.log1p((r - p) / (p * n.astype(np.float64)))
            )
        cell_variation *= last_weight
        scale = p ** (2 - 2 * s.real)
        for q in BASES:
            if p == q:
                continue
            key = str(p) + "," + str(q)
            direct = np.cumsum(c * tails[q] * cell_variation)
            vals = [complex(direct[N - 1]) for N in CUTOFFS]
            correction[key] = [packed(v) for v in vals]
            assembled = [
                complex(*mixed[str(p * q)][i])
                - complex(*mixed[str(p)][i])
                - scale * complex(*mixed[str(q)][i])
                for i in range(len(CUTOFFS))
            ]
            # Distinct finite cutoffs: this is a convergence diagnostic,
            # not an assertion of exact equality at finite N.
            identity_error[key] = [abs(a - b) for a, b in zip(assembled, vals)]
    return {
        "spec": spec,
        "s": packed(s),
        "height_70_digits": str(height),
        "zeta": packed(zeta),
        "T": mixed,
        "J": correction,
        "tail_endpoints": endpoints,
        "insertion_limit_error": identity_error,
        "seconds": time.time() - start,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="results.json")
    parser.add_argument("--workers", type=int, default=8)
    args = parser.parse_args()
    specs = [
        {"sigma": "0.5", "zero": j, "label": "zero-" + str(j)}
        for j in range(1, 9)
    ]
    specs += [
        {"sigma": sigma, "zero": j, "label": "shift-" + sigma + "-" + str(j)}
        for sigma in ("0.65", "0.85") for j in (1, 2, 3)
    ]
    specs += [
        {"sigma": "1.25", "height": "0", "label": "absolute-real"},
        {"sigma": "0.5", "height": "17", "label": "line-nonzero"},
    ]
    workers = min(args.workers, os.cpu_count() or 1, len(specs))
    start = time.time()
    results = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
        for row in pool.map(task, specs):
            results.append(row)
            vals = [complex(*v[-1]) for v in row["J"].values()]
            drift = max(
                abs(complex(*v[-1]) - complex(*v[-2]))
                for v in row["J"].values()
            )
            print(row["spec"]["label"], "max|J|=", max(map(abs, vals)),
                  "max cutoff drift=", drift, flush=True)
    payload = {
        "description": "Exploratory mixed within-cell correction, not a proof",
        "cutoffs": CUTOFFS,
        "bases": BASES,
        "workers": workers,
        "python": platform.python_version(),
        "numpy": np.__version__,
        "mpmath": mp.__version__,
        "seconds": time.time() - start,
        "results": results,
    }
    with open(args.output, "w", encoding="utf-8") as out:
        json.dump(payload, out, indent=2)


if __name__ == "__main__":
    main()
