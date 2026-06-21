#!/usr/bin/env python3
"""THE-MACHINE Step 11: branching-spine visual metaphor.

Metaphor:
    A terminal survivor lights up a backward ancestry spine through a branching
    forest. In branching theory the "right theorem" is a Doob/many-to-one
    transform: a survival weight h(state) changes the forward law into the
    backward spine law.

Wild HT test:
    Treat dyadic vertical intervals as coarse states in the continuum phase
    field. Fit a simple local h-weight from boundary values of the phase-defect
    interval to the fraction of terminal positive leaves inside it. Then test
    whether that weight ports across windows and controls.

Reduce-to-known gate:
    If true zeta, finite Euler, and random controls all admit comparable local
    h-weights, or if the result is just endpoint interpolation/run persistence,
    this is a dead end. Only a portable true-specific gap would be noteworthy.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def phase_series(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> np.ndarray:
    vals: list[float] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(max(0.0, phase_defect(g, p)))
    return np.asarray(vals, dtype=float)


def interval_dataset(values: np.ndarray, threshold: float) -> tuple[np.ndarray, np.ndarray]:
    rows: list[list[float]] = []
    targets: list[float] = []
    n = len(values)
    for level in [3, 4, 5, 6, 7]:
        bins = 2**level
        width = n // bins
        if width < 4:
            continue
        trimmed = values[: bins * width]
        for idx in range(bins):
            segment = trimmed[idx * width : (idx + 1) * width]
            left = float(segment[0])
            right = float(segment[-1])
            center = float((left + right) / 2.0)
            slope = float(right - left)
            boundary_min = min(left, right)
            boundary_max = max(left, right)
            rows.append(
                [
                    1.0,
                    level / 7.0,
                    math.log2(width) / math.log2(n),
                    left,
                    right,
                    center,
                    slope,
                    abs(slope),
                    boundary_min,
                    boundary_max,
                    float(left > threshold),
                    float(right > threshold),
                ]
            )
            targets.append(float(np.mean(segment > threshold)))
    return np.asarray(rows, dtype=float), np.asarray(targets, dtype=float)


def standardize_train_test(x_train: np.ndarray, x_test: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    out_train = np.array(x_train, copy=True)
    out_test = np.array(x_test, copy=True)
    for j in range(1, x_train.shape[1]):
        mu = float(np.mean(x_train[:, j]))
        sd = float(np.std(x_train[:, j]))
        if sd < 1e-12:
            sd = 1.0
        out_train[:, j] = (out_train[:, j] - mu) / sd
        out_test[:, j] = (out_test[:, j] - mu) / sd
    return out_train, out_test


def fit_ridge(x: np.ndarray, y: np.ndarray, lam: float) -> np.ndarray:
    reg = lam * np.eye(x.shape[1])
    reg[0, 0] = 0.0
    return np.linalg.solve(x.T @ x + reg, x.T @ y)


def metrics(y: np.ndarray, pred: np.ndarray) -> tuple[float, float, float]:
    pred = np.clip(pred, 0.0, 1.0)
    err = y - pred
    denom = float(np.sum((y - float(np.mean(y))) ** 2))
    r2 = 1.0 - float(np.sum(err * err)) / max(denom, 1e-12)
    corr = float(np.corrcoef(y, pred)[0, 1]) if float(np.std(y)) > 1e-12 and float(np.std(pred)) > 1e-12 else 0.0
    mae = float(np.mean(np.abs(err)))
    return r2, corr, mae


def run_h_transform(samples: int, prime_count: int, threshold: float, lam: float) -> None:
    primes = first_primes(prime_count)
    rng = np.random.default_rng(260621183)
    train_window = (14.0, 84.0)
    test_windows = [(100.0, 170.0), (500.0, 570.0)]
    kinds = ["true", "finite", "random"]
    sigmas = [0.5, 0.7, 1.2]
    print("STEP11 h-transform metaphor: local boundary survival weight")
    print(f"samples={samples} prime_count={prime_count} threshold={threshold} ridge={lam}")
    print("Train on sigma=0.5 window=[14,84], then port the h-weight.")
    print("train_kind test_kind sigma test_window r2 corr mae target_mean pred_mean")

    train_sets: dict[str, tuple[np.ndarray, np.ndarray]] = {}
    for kind in kinds:
        vals = phase_series(kind, 0.5, train_window, samples, primes, rng)
        train_sets[kind] = interval_dataset(vals, threshold)

    test_sets: dict[tuple[str, float, tuple[float, float]], tuple[np.ndarray, np.ndarray]] = {}
    for sigma in sigmas:
        for window in test_windows:
            for kind in kinds:
                vals = phase_series(kind, sigma, window, samples, primes, rng)
                test_sets[(kind, sigma, window)] = interval_dataset(vals, threshold)

    for train_kind, (x_train_raw, y_train) in train_sets.items():
        for sigma in sigmas:
            for window in test_windows:
                for test_kind in kinds:
                    x_test_raw, y_test = test_sets[(test_kind, sigma, window)]
                    x_train, x_test = standardize_train_test(x_train_raw, x_test_raw)
                    beta = fit_ridge(x_train, y_train, lam)
                    pred = x_test @ beta
                    r2, corr, mae = metrics(y_test, pred)
                    print(
                        f"{train_kind:6s} {test_kind:6s} {sigma:.1f} "
                        f"[{window[0]:.0f},{window[1]:.0f}] {r2:+.3f} {corr:+.3f} {mae:.3f} "
                        f"{float(np.mean(y_test)):.3f} {float(np.mean(np.clip(pred,0,1))):.3f}"
                    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=0.0)
    parser.add_argument("--ridge", type=float, default=0.1)
    args = parser.parse_args()
    run_h_transform(args.samples, args.prime_count, args.threshold, args.ridge)


if __name__ == "__main__":
    main()
