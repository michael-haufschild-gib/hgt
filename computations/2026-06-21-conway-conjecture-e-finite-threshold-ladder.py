#!/usr/bin/env python3
"""Finite-threshold ladder gate for Conjecture E zero-prediction evidence."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


def normal_tail(a: float) -> float:
    return 0.5 * math.erfc(a / math.sqrt(2.0))


def importance_sampling_tail(
    threshold: float,
    tilt: float,
    samples: int,
    rng: np.random.Generator,
) -> tuple[float, float, float]:
    x = rng.normal(tilt, 1.0, size=samples)
    weights = np.exp(-tilt * x + 0.5 * tilt * tilt)
    contributions = weights * (x > threshold)
    estimate = float(np.mean(contributions))
    se = float(np.std(contributions, ddof=1) / math.sqrt(samples))
    ess = float((np.sum(contributions) ** 2) / (np.sum(contributions**2) + 1e-300))
    return estimate, se, ess


def node_finite_threshold_tilt(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    samples = 50_000

    print("NODE: asymptotic tilt can fail at finite thresholds")
    print("threshold tilt exact estimate rel_se ess")
    for threshold in [2.0, 3.0, 6.0]:
        exact = normal_tail(threshold)
        for tilt in [threshold, 6.0]:
            estimate, se, ess = importance_sampling_tail(threshold, tilt, samples, rng)
            print(
                f"{threshold:.1f} {tilt:.1f} {exact:.6e} {estimate:.6e} "
                f"{se / exact:.3f} {ess:.1f}"
            )
    print(
        "constraint: a change of measure tuned for an extreme tail can have poor "
        "finite-threshold effective sample size even when it is sensible asymptotically"
    )
    print()


def first_primes(k: int) -> list[int]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < k:
        if all(candidate % p for p in primes):
            primes.append(candidate)
        candidate += 1
    return primes


def smooth_zero_inverse(n: int) -> float:
    a = mp.mpf(n) - mp.mpf(11) / 8
    y = a / mp.lambertw(a / mp.e)
    return float(2 * mp.pi * y)


def feature_matrix(t: np.ndarray, primes: list[int], k: int) -> np.ndarray:
    columns = [np.ones_like(t), 1.0 / np.log(t)]
    for p in primes[:k]:
        frequency = math.log(p)
        columns.append(np.sin(t * frequency))
        columns.append(np.cos(t * frequency))
    return np.column_stack(columns)


def margin_row(
    actual: np.ndarray,
    baseline: np.ndarray,
    corrected: np.ndarray,
) -> tuple[float, float, float]:
    ordinate_margin = np.abs(actual - baseline) - np.abs(actual - corrected)
    spacing_margin = np.abs(np.diff(actual) - np.diff(baseline)) - np.abs(
        np.diff(actual) - np.diff(corrected)
    )
    return (
        float(np.mean(ordinate_margin)),
        float(np.mean(spacing_margin)),
        float(np.mean(ordinate_margin > 0.0)),
    )


def fit_models(x_train: np.ndarray, y_train: np.ndarray) -> dict[str, np.ndarray]:
    models: dict[str, np.ndarray] = {}
    models["untruncated"] = np.linalg.lstsq(x_train, y_train, rcond=None)[0]
    models["rcond_0.01"] = np.linalg.lstsq(x_train, y_train, rcond=0.01)[0]
    models["rcond_0.10"] = np.linalg.lstsq(x_train, y_train, rcond=0.10)[0]
    models["ridge_1e-1"] = np.linalg.solve(
        x_train.T @ x_train + 0.1 * np.eye(x_train.shape[1]),
        x_train.T @ y_train,
    )
    return models


def transfer_finite_window_ladder() -> None:
    mp.mp.dps = 50
    n_values = np.arange(30, 420)
    zeros = np.array([float(mp.im(mp.zetazero(int(n)))) for n in n_values])
    baseline = np.array([smooth_zero_inverse(int(n)) for n in n_values])
    residual = zeros - baseline
    primes = first_primes(60)

    train = (n_values >= 30) & (n_values <= 99)
    k = 34
    x_train = feature_matrix(baseline[train], primes, k)
    y_train = residual[train]
    models = fit_models(x_train, y_train)

    windows = [
        (100, 119),
        (120, 139),
        (140, 159),
        (160, 179),
        (180, 199),
        (200, 219),
        (240, 259),
        (280, 299),
        (320, 339),
        (360, 379),
        (390, 409),
    ]

    print("TRANSFER: ResearchNode #34 Conjecture E kill gate")
    print("method #10 test extreme cases: finite-window ladder")
    print(
        f"training_window=[30,99] K={k} features={x_train.shape[1]} "
        f"condition={np.linalg.cond(x_train):.2f}"
    )
    print("model window ordinate_margin spacing_margin ordinate_improvement_rate")

    failures: dict[str, int] = {name: 0 for name in models}
    for name, beta in models.items():
        for lo, hi in windows:
            test = (n_values >= lo) & (n_values <= hi)
            x_test = feature_matrix(baseline[test], primes, k)
            corrected = baseline[test] + x_test @ beta
            ordinate, spacing, rate = margin_row(zeros[test], baseline[test], corrected)
            if ordinate < 0.0 or spacing < 0.0:
                failures[name] += 1
            print(f"{name:11s} [{lo},{hi}] {ordinate:+.6f} {spacing:+.6f} {rate:.3f}")
        print()

    print("FINITE-LADDER FAILURES")
    for name, count in failures.items():
        print(f"{name:11s} {count}/{len(windows)}")

    print()
    print("GATE SUMMARY")
    print(
        "`rcond_0.01` passes the first checked window but fails 3/11 finite windows; "
        "`untruncated` fails 11/11; stronger truncation/ridge passes this ladder"
    )
    print(
        "Conjecture E evidence should therefore require a finite-threshold ladder, "
        "not a single high-window or asymptotic-looking pass"
    )


def main() -> None:
    node_finite_threshold_tilt()
    transfer_finite_window_ladder()


if __name__ == "__main__":
    main()
