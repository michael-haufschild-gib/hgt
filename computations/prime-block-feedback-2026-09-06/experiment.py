"""Run on the authorized pod. Numerical evidence only; no Lean inputs."""
import argparse
import json
import multiprocessing as mp
import os
import time
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss

ROOT = Path(__file__).resolve().parent
END = 90**4
LAGS = 8
BASE_PRIMES = None
PRIMES = None


def small_sieve(n):
    a = np.ones(n + 1, dtype=bool)
    a[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if a[p]:
            a[p*p::p] = False
    return np.flatnonzero(a)


def segment(bounds):
    lo, hi = bounds
    a = np.ones(hi - lo, dtype=bool)
    for p in BASE_PRIMES:
        start = max(p*p, ((lo + p - 1)//p)*p)
        if start < hi:
            a[start-lo::p] = False
    if lo < 2:
        a[:2-lo] = False
    return np.flatnonzero(a).astype(np.int64) + lo


def build_primes():
    global BASE_PRIMES
    path = ROOT / "primes.npy"
    if path.exists():
        return np.load(path, mmap_mode="r")
    BASE_PRIMES = small_sieve(int(END**0.5) + 1)
    step = 2**21
    bounds = [(lo, min(END, lo+step)) for lo in range(0, END, step)]
    with mp.get_context("fork").Pool(8) as pool:
        p = np.concatenate(pool.map(segment, bounds))
    # Separate implementation checks, not evidence for an analytic bound.
    assert np.array_equal(p, small_sieve(END-1))
    assert np.all(p[1:] > p[:-1]) and p[0] == 2 and p[-1] < END
    np.save(path, p)
    return p


def reference(a, b, order):
    z, w = leggauss(order)
    mid = (a+b)/2
    x = mid + (b-a)*z/2
    weights = (b-a)*w/(2*np.log(x))
    coordinate = np.log(x/mid)
    mass = float(weights.sum())
    center = float(weights @ coordinate / mass)
    variance = float(weights @ ((coordinate-center)**2))
    return mass, center, variance


def make_rows(r):
    rows = []
    quadrature_error = np.zeros(3)
    for k in range(4, 90):
        edges = k**4 + ((np.arange(r+1, dtype=np.int64)*((k+1)**4-k**4))//r)
        for j, (a, b) in enumerate(zip(edges[:-1], edges[1:])):
            low, high = np.searchsorted(PRIMES, [a, b], side="left")
            p = PRIMES[low:high]
            mass, center, variance = reference(a, b, 32)
            refined = np.array(reference(a, b, 64))
            quadrature_error = np.maximum(quadrature_error,
                np.abs(refined-np.array([mass, center, variance])) /
                np.maximum(np.abs(refined), [1., 1e-12, 1e-12]))
            mid = (a+b)/2
            dipole = float(np.sum(np.log(p.astype(float)/mid)-center))
            A = (len(p)-mass)/np.sqrt(mass)
            B = dipole/np.sqrt(variance)
            rows.append([k, j, a, b, len(p), mass, center, variance, A, B])
    a = np.asarray(rows, dtype=float)
    np.savez_compressed(ROOT/f"rows-r{r}.npz", rows=a)
    return {"resolution": r, "rows": len(rows),
            "quadrature_relative_error": quadrature_error.tolist()}


def design(rows, include_dipole, reverse=False):
    ix = np.arange(LAGS, len(rows)) if not reverse else np.arange(len(rows)-LAGS)
    offsets = -np.arange(1, LAGS+1) if not reverse else np.arange(1, LAGS+1)
    past = ix[:, None] + offsets
    x = rows[past, 8]
    if include_dipole:
        x = np.concatenate([x, rows[past, 9]], axis=1)
    return ix, past, x, rows[ix, 8]


def fit(x, y):
    mean = x.mean(axis=0)
    scale = x.std(axis=0)
    scale = np.maximum(scale, 1e-12)
    z = (x-mean)/scale
    intercept = float(y.mean())
    coef = np.linalg.solve(z.T@z + 1e-3*np.eye(z.shape[1]), z.T@(y-intercept))
    return {"mean": mean.tolist(), "scale": scale.tolist(),
            "intercept": intercept, "coef": coef.tolist()}


def predict(model, x):
    return (x-np.asarray(model["mean"]))/np.asarray(model["scale"]) @ np.asarray(model["coef"]) + model["intercept"]


def summarize_fit(rows, reverse=False):
    results = {}
    for dipole in [False, True]:
        name = "count_and_dipole" if dipole else "count_only"
        ix, past, x, y = design(rows, dipole, reverse)
        train = (rows[ix, 0] < 24) & np.all(rows[past, 0] < 24, axis=1)
        screen = (rows[ix, 0] >= 24) & (rows[ix, 0] < 32)
        if not screen.any():
            return {"status": "not_estimable_no_screen_rows",
                    "dipole_improvement": None, "baseline_improvement": None}
        model = fit(x[train], y[train])
        pred = predict(model, x[screen])
        results[name] = {"model": model, "train_n": int(train.sum()),
            "screen_n": int(screen.sum()), "mse": float(np.mean((pred-y[screen])**2)),
            "baseline_mse": float(np.mean((y[screen]-model["intercept"])**2))}
    results["dipole_improvement"] = 1-results["count_and_dipole"]["mse"]/results["count_only"]["mse"]
    results["baseline_improvement"] = 1-results["count_and_dipole"]["mse"]/results["count_and_dipole"]["baseline_mse"]
    return results


def discovery():
    out = {"phase": "discovery", "data_peek_limit_k": 31, "resolutions": {}}
    for r in [1, 4, 16]:
        rows = np.load(ROOT/f"rows-r{r}.npz")["rows"]
        rows = rows[rows[:, 0] < 32]
        corrs = []
        for lag in range(1, LAGS+1):
            corrs.append({"lag": lag, "AA": float(np.corrcoef(rows[:-lag,8], rows[lag:,8])[0,1]),
                "BA_forward": float(np.corrcoef(rows[:-lag,9], rows[lag:,8])[0,1]),
                "AB_forward": float(np.corrcoef(rows[:-lag,8], rows[lag:,9])[0,1])})
        out["resolutions"][str(r)] = {"forward": summarize_fit(rows),
            "backward": summarize_fit(rows, True), "correlations": corrs,
            "observed_covariance": np.cov(rows[:,8:10].T).tolist()}
    d = out["resolutions"]["16"]["forward"]
    out["advance"] = d["dipole_improvement"] >= .05 and d["baseline_improvement"] >= .05
    (ROOT/"discovery.json").write_text(json.dumps(out, indent=2))
    print(json.dumps({"phase": out["phase"], "advance": out["advance"],
        "metrics": {r: {d: {k: v[k] for k in ["dipole_improvement", "baseline_improvement"]}
                    for d, v in entry.items() if d in ["forward", "backward"]}
                    for r, entry in out["resolutions"].items()}}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=["prepare", "discovery"])
    args = parser.parse_args()
    start = time.monotonic()
    if args.phase == "prepare":
        PRIMES = build_primes()
        with mp.get_context("fork").Pool(3) as pool:
            checks = pool.map(make_rows, [1, 4, 16])
        metadata = {"end_exclusive": END, "prime_count": len(PRIMES), "checks": checks,
                    "wall_seconds": time.monotonic()-start,
                    "workers_sieve": 8, "workers_rows": 3}
        (ROOT/"metadata.json").write_text(json.dumps(metadata, indent=2))
        print(json.dumps(metadata, indent=2))
    else:
        discovery()
        print("wall_seconds", time.monotonic()-start)
