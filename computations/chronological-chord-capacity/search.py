"""Exploratory search only: signed versus monotone chord-polynomial capacity.

Run on the authorized Runpod. No output of this script is a proof certificate.
Each worker owns one random stream; BLAS threads are disabled before NumPy loads.
"""
import os
for key in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
    os.environ[key] = "1"

import itertools
import json
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np
from scipy.optimize import minimize


def matchings(points):
    if not points:
        return [()]
    result = []
    for j in range(1, len(points), 2):
        for left in matchings(points[1:j]):
            for right in matchings(points[j + 1:]):
                result.append(((points[0], points[j]),) + left + right)
    return result


DIAGRAMS = matchings(tuple(range(6)))
INCIDENCE = np.array([[[int(a <= k < b) for k in range(5)]
                       for a, b in d] for d in DIAGRAMS], dtype=float)
COEFFICIENTS = np.array([c for c in itertools.product((-1, 0, 1), repeat=5)
                         if next((x for x in c if x), 0) == 1], dtype=float)


def values(x):
    return np.prod(np.einsum("dri,ni->ndr", INCIDENCE, x), axis=2)


def sample(seed):
    rng = np.random.default_rng(seed)
    best_pos = np.zeros(len(COEFFICIENTS))
    best_signed = np.zeros(len(COEFFICIENTS))
    for _ in range(12):
        x = rng.dirichlet(np.full(5, 0.3), size=6000)
        best_pos = np.maximum(best_pos, np.max(np.abs(values(x) @ COEFFICIENTS.T), axis=0))
        x *= rng.choice((-1, 1), size=x.shape)
        best_signed = np.maximum(best_signed,
                                 np.max(np.abs(values(x) @ COEFFICIENTS.T), axis=0))
    return best_pos, best_signed


def optimize(args):
    c, signed = args
    rng = np.random.default_rng(873)
    starts = list(np.eye(5)) + [np.full(5, .2)]
    starts += list(rng.dirichlet(np.ones(5), size=8))
    best = {"value": 0.0, "increments": []}
    signs = itertools.product((-1, 1), repeat=4) if signed else [(1, 1, 1, 1)]
    for tail in signs:
        sign = np.array((1,) + tuple(tail))
        inc = INCIDENCE * sign

        def polynomial(z):
            sums = inc @ z
            return float(c @ np.prod(sums, axis=1))

        def gradient(z):
            sums = inc @ z
            result = np.zeros(5)
            for j in range(3):
                result += np.einsum("d,di->i", c * np.prod(np.delete(sums, j, axis=1), axis=1),
                                    inc[:, j, :])
            return result

        for direction in (-1, 1):
            for start in starts:
                result = minimize(lambda z: direction * polynomial(z), start,
                                  jac=lambda z: direction * gradient(z),
                                  bounds=[(0, 1)] * 5,
                                  constraints={"type": "eq", "fun": lambda z: z.sum() - 1,
                                               "jac": lambda z: np.ones(5)},
                                  method="SLSQP", options={"ftol": 1e-12, "maxiter": 120})
                if result.success and abs(polynomial(result.x)) > best["value"]:
                    best = {"value": abs(polynomial(result.x)),
                            "increments": (result.x * sign).tolist()}
    return {"coefficients": c.tolist(), "signed": signed, **best}


if __name__ == "__main__":
    workers = min(24, os.cpu_count() or 1)
    with ProcessPoolExecutor(max_workers=workers) as pool:
        sampled = list(pool.map(sample, range(32)))
        pos = np.max([r[0] for r in sampled], axis=0)
        signed = np.max([r[1] for r in sampled], axis=0)
        order = np.argsort(signed / np.maximum(pos, 1e-15))[::-1][:12]
        jobs = [(COEFFICIENTS[i], s) for i in order for s in (False, True)]
        results = list(pool.map(optimize, jobs))
    payload = {"purpose": "Find a strict signed-path advantage, not certify optimality",
               "workers": workers, "seed_range": [0, 31],
               "samples_per_worker_per_class": 72000,
               "diagrams": DIAGRAMS, "coefficient_vectors_tested": len(COEFFICIENTS),
               "results": results}
    Path("results.json").write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2), flush=True)
