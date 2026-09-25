"""Test the stronger normalized noncrossing-basis inequality; numerical leads only."""
import os
for key in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
    os.environ[key] = "1"
import json
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from search import matchings


def capacity(diagram):
    if not diagram:
        return Fraction(1)
    a, b = diagram[0]
    inside = tuple(e for e in diagram[1:] if a < e[0] < b)
    outside = tuple(e for e in diagram[1:] if e[0] > b)
    p, q = len(inside) + 1, len(outside)
    factor = Fraction(p**p * (q**q if q else 1), (p+q)**(p+q))
    return factor * capacity(inside) * capacity(outside)


def probe(args):
    r, seed, signed = args
    rng = np.random.default_rng(seed)
    diagrams = matchings(tuple(range(2*r)))
    inc = np.array([[[int(a <= k < b) for k in range(2*r-1)]
                     for a, b in d] for d in diagrams], dtype=float)
    weights = 1 / np.array([float(capacity(d)) for d in diagrams])
    x = rng.dirichlet(np.full(2*r-1, .3), size=2500)
    if signed:
        x *= rng.choice((-1, 1), size=x.shape)
    vals = np.prod(np.einsum("dri,ni->ndr", inc, x), axis=2)
    score = np.abs(vals) @ weights
    best = {"value": float(score.max()), "increments": x[score.argmax()].tolist()}
    for k in np.argsort(score)[-12:]:
        signs = np.where(x[k] < 0, -1, 1)
        ainc = inc * signs

        def fun(z):
            sums = ainc @ z
            vals = np.prod(sums, axis=1)
            grad = np.zeros(2*r-1)
            for j in range(r):
                grad += np.einsum("d,di->i", weights * np.sign(vals) *
                                  np.prod(np.delete(sums, j, axis=1), axis=1), ainc[:, j, :])
            return -float(weights @ np.abs(vals)), -grad

        res = minimize(fun, np.abs(x[k]), jac=True, method="SLSQP",
                       bounds=[(0, 1)]*(2*r-1),
                       constraints={"type": "eq", "fun": lambda z: z.sum()-1,
                                    "jac": lambda z: np.ones(2*r-1)},
                       options={"maxiter": 250, "ftol": 1e-12})
        if res.success and -res.fun > best["value"]:
            best = {"value": -float(res.fun), "increments": (signs*res.x).tolist()}
    return {"r": r, "seed": seed, "signed": signed, **best}


if __name__ == "__main__":
    jobs = [(r, s, signed) for r in range(2, 7) for s in range(6) for signed in (False, True)]
    with ProcessPoolExecutor(max_workers=24) as pool:
        results = list(pool.map(probe, jobs))
    Path("basis-results.json").write_text(json.dumps(results, indent=2)+"\n")
    for r in range(2, 7):
        for signed in (False, True):
            print(max((x for x in results if x["r"] == r and x["signed"] == signed),
                      key=lambda x: x["value"]), flush=True)
