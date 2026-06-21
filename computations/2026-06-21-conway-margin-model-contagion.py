#!/usr/bin/env python3
"""THE-MACHINE run: margin-model contagion.

NODE:
    Arbitrage books can become correlated through margin models, not just
    through asset returns.

STEP 5 constraint:
    A funding/margin inequality creates a common liquidation boundary:

        loss_i(t) + model_margin_i(t) > maintenance_threshold.

    The asset returns may be nearly uncorrelated while liquidation/cut events
    become synchronized because the same margin model or funding stress enters
    every book.

STEP 8 selected transfer:
    Replace arbitrage books by vertical sigma-lanes of the continuum
    differential field x_sigma(t)=log(1+|d/ds log f(sigma+it)|). The "asset
    return" is the vertical increment of x_sigma. The shared margin model is a
    tail stress of the completed weld log-derivative |Gamma_infty + P|.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from typing import Callable

import mpmath as mp
import numpy as np


def corr_safe(a: np.ndarray, b: np.ndarray) -> float:
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    if a.size < 3 or b.size < 3:
        return float("nan")
    if float(np.std(a)) < 1e-12 or float(np.std(b)) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def zscore(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    sd = float(np.std(x))
    if sd < 1e-12:
        return np.zeros_like(x)
    return (x - float(np.mean(x))) / sd


def positive_tail(x: np.ndarray) -> np.ndarray:
    return np.maximum(0.0, zscore(x))


def binary_corr(events: np.ndarray) -> float:
    a = events[0].astype(float)
    b = events[1].astype(float)
    return corr_safe(a, b)


def liquidation_metrics(
    levels: np.ndarray,
    common_stress: np.ndarray,
    margin_weight: float = 1.30,
    q: float = 0.93,
) -> dict[str, float]:
    """Compare asset-return correlation with margin-call correlation.

    levels has shape (2, n). common_stress has length n. Thresholds are set
    within each model so event frequency is comparable; the discriminant is the
    correlation lift from the shared model against lane-shifted controls.
    """

    returns = np.diff(levels, axis=1)
    losses = np.maximum(0.0, -returns)
    stress = positive_tail(common_stress[1:])
    if stress.size != losses.shape[1]:
        stress = stress[: losses.shape[1]]

    pressure_common = losses + margin_weight * stress[None, :]
    threshold_common = float(np.quantile(pressure_common.reshape(-1), q))
    calls_common = pressure_common > threshold_common

    shift = max(7, stress.size // 3)
    stress_lane = np.vstack([np.roll(stress, shift), np.roll(stress, 2 * shift)])
    pressure_shifted = losses + margin_weight * stress_lane
    threshold_shifted = float(np.quantile(pressure_shifted.reshape(-1), q))
    calls_shifted = pressure_shifted > threshold_shifted

    loss_threshold = float(np.quantile(losses.reshape(-1), q))
    calls_loss_only = losses > loss_threshold

    return {
        "raw_return_corr": corr_safe(returns[0], returns[1]),
        "loss_call_corr": binary_corr(calls_loss_only),
        "shared_margin_corr": binary_corr(calls_common),
        "shifted_margin_corr": binary_corr(calls_shifted),
        "shared_event_rate": float(np.mean(calls_common)),
        "margin_lift_vs_raw": binary_corr(calls_common) - abs(corr_safe(returns[0], returns[1])),
        "margin_lift_vs_shift": binary_corr(calls_common) - binary_corr(calls_shifted),
    }


def ar1(rng: np.random.Generator, n: int, phi: float = 0.94) -> np.ndarray:
    x = np.zeros(n)
    eps = rng.normal(size=n)
    for i in range(1, n):
        x[i] = phi * x[i - 1] + eps[i]
    return zscore(x)


def financial_node_simulation(seed: int = 20260621, n: int = 5000) -> None:
    rng = np.random.default_rng(seed)
    print("NODE simulation: correlated through margin model, not only asset returns")
    print("case raw_return_corr loss_call_corr shared_margin_corr shifted_margin_corr lift_vs_raw lift_vs_shift event_rate")
    for name, asset_corr, shared_margin in [
        ("neither", 0.00, False),
        ("asset_only", 0.75, False),
        ("shared_margin_only", 0.00, True),
        ("asset_plus_margin", 0.75, True),
    ]:
        cov = np.array([[1.0, asset_corr], [asset_corr, 1.0]])
        returns = rng.multivariate_normal([0.0, 0.0], cov, size=n).T * 0.012
        levels = np.cumsum(returns, axis=1)
        if shared_margin:
            stress = ar1(rng, n)
        else:
            # Different margin models per lane: the common input is destroyed.
            stress = ar1(rng, n)
            levels = levels + 0.0 * stress[None, :]
        if not shared_margin:
            # The metrics routine expects one stress series, then constructs a
            # shifted-lane control. Set margin_weight=0 so calls are genuinely
            # loss-driven in the no-shared-margin boundary case.
            metrics = liquidation_metrics(levels, stress, margin_weight=0.0)
        else:
            metrics = liquidation_metrics(levels, stress, margin_weight=1.30)
        print(
            f"{name:18s} "
            f"{metrics['raw_return_corr']:+.3f} "
            f"{metrics['loss_call_corr']:+.3f} "
            f"{metrics['shared_margin_corr']:+.3f} "
            f"{metrics['shifted_margin_corr']:+.3f} "
            f"{metrics['margin_lift_vs_raw']:+.3f} "
            f"{metrics['margin_lift_vs_shift']:+.3f} "
            f"{metrics['shared_event_rate']:.3f}"
        )


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[j - 1] + 1,
                    prev[j - 1] + (0 if ca == cb else 1),
                )
            )
        prev = cur
    return prev[-1]


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


def dlog_random_phase_zeta(s: complex, rng: np.random.Generator) -> complex:
    base = dlog_zeta(s)
    theta = rng.uniform(-math.pi, math.pi)
    return abs(base) * complex(math.cos(theta), math.sin(theta))


@dataclass(frozen=True)
class Candidate:
    name: str
    component: Callable[[complex], complex]


def ht_levels(
    component: Callable[[complex], complex],
    sigmas: tuple[float, float],
    window: tuple[float, float],
    samples: int,
) -> tuple[np.ndarray, np.ndarray]:
    t0, t1 = window
    ts = np.linspace(t0, t1, samples)
    levels = []
    stress = []
    for sigma in sigmas:
        lane = []
        lane_stress = []
        for t in ts:
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            p = component(s)
            lane.append(math.log1p(abs(p)))
            lane_stress.append(math.log1p(abs(g + p)))
        levels.append(lane)
        stress.append(lane_stress)
    shared_stress = np.max(np.asarray(stress, dtype=float), axis=0)
    return np.asarray(levels, dtype=float), shared_stress


def ht_boundary_run(samples: int, prime_count: int) -> list[dict[str, float | str]]:
    primes = first_primes(prime_count)
    rng = np.random.default_rng(90210)
    candidates = [
        Candidate("true_zeta", dlog_zeta),
        Candidate("finite_euler", lambda s: dlog_finite_euler(s, primes)),
        Candidate("random_phase", lambda s: dlog_random_phase_zeta(s, rng)),
        Candidate("gamma_only", gamma_part),
    ]
    windows = [(100.0, 170.0), (500.0, 570.0)]
    sigmas = (0.3, 0.7)
    rows: list[dict[str, float | str]] = []
    for window in windows:
        for candidate in candidates:
            levels, stress = ht_levels(candidate.component, sigmas, window, samples)
            metrics = liquidation_metrics(levels, stress, margin_weight=1.30, q=0.93)
            row: dict[str, float | str] = {
                "candidate": candidate.name,
                "window": f"[{window[0]:g},{window[1]:g}]",
                **metrics,
            }
            rows.append(row)
    return rows


def print_ht_transfer(samples: int, prime_count: int) -> None:
    node_kernel = "returns losses shared_margin pressure threshold calls correlation"
    attempts = {
        "A_sigma_lane_shared_margin": "returns vertical increments losses shared_weld_margin pressure threshold calls correlation",
        "B_phase_carrier_haircut": "phase defect carrier haircut antiphase threshold parasite selection",
        "C_zero_redemption_network": "zero proximity redemption network graph cascade hitting time",
    }
    distances = {name: levenshtein(node_kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:30s} distance={dist}")
    print(f"selected={selected}")

    print("\nSTEP8/9 HT transfer: classify boundary cases")
    print("sigmas=0.3,0.7; levels=log(1+|P|); shared margin stress=max_sigma log(1+|Gamma_inf+P|)")
    print(
        "candidate window raw_return_corr loss_call_corr shared_margin_corr "
        "shifted_margin_corr lift_vs_raw lift_vs_shift event_rate"
    )
    rows = ht_boundary_run(samples=samples, prime_count=prime_count)
    for row in rows:
        print(
            f"{row['candidate']:12s} {row['window']:9s} "
            f"{row['raw_return_corr']:+.3f} "
            f"{row['loss_call_corr']:+.3f} "
            f"{row['shared_margin_corr']:+.3f} "
            f"{row['shifted_margin_corr']:+.3f} "
            f"{row['margin_lift_vs_raw']:+.3f} "
            f"{row['margin_lift_vs_shift']:+.3f} "
            f"{row['shared_event_rate']:.3f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()
    np.set_printoptions(precision=4, suppress=True)
    financial_node_simulation()
    print_ht_transfer(samples=args.samples, prime_count=args.prime_count)


if __name__ == "__main__":
    main()
