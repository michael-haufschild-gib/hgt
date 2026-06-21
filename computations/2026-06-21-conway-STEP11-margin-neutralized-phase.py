#!/usr/bin/env python3
"""STEP 11 for margin-model contagion.

Metaphor:
    A margin model can manufacture synchronized liquidations that are not in
    the underlying asset returns. For HT probes, an amplitude/common-stress
    variable can likewise manufacture apparent coupling. The wild experiment:
    neutralize the shared margin variables and ask whether the phase-carrier
    defect survives as residual structure.

This is a control on the ultradiscrete phase-carrier observable

    Delta = max(log|G|, log|P|) - log|G+P|,

where G is the archimedean Gamma log-derivative contribution and P is a prime
or zeta log-derivative contribution.
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


def defect_and_features(g: complex, p: complex) -> tuple[float, list[float]]:
    ag = abs(g)
    ap = abs(p)
    at = abs(g + p)
    delta = math.log(max(ag, ap) + 1e-300) - math.log(at + 1e-300)
    cos = 0.0
    if ag > 1e-300 and ap > 1e-300:
        cos = float((g * p.conjugate()).real / (ag * ap))
    # "Margin variables": amplitude/collateral quantities only. The phase
    # cosine and |G+P| are intentionally omitted from the regression; |G+P|
    # already contains the destructive-interference term that defines Delta.
    # If phase explains the effect, it should survive this neutralization.
    features = [
        1.0,
        math.log1p(ag),
        math.log1p(ap),
        math.log((ap + 1e-300) / (ag + 1e-300)),
        math.log1p(max(ag, ap)),
        math.log1p(min(ag, ap)),
    ]
    return delta, features


def rows_for(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator):
    t0, t1 = window
    deltas = []
    feats = []
    for t in np.linspace(t0, t1, samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random_phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        delta, features = defect_and_features(g, p)
        deltas.append(delta)
        feats.append(features)
    return np.asarray(deltas, dtype=float), np.asarray(feats, dtype=float)


def summarize_case(sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...]) -> dict[str, float]:
    rng = np.random.default_rng(60621 + int(1000 * sigma) + int(window[0]))
    true_delta, true_x = rows_for("true", sigma, window, samples, primes, rng)
    finite_delta, finite_x = rows_for("finite", sigma, window, samples, primes, rng)
    rand_delta, rand_x = rows_for("random_phase", sigma, window, samples, primes, rng)

    control_x = np.vstack([finite_x, rand_x])
    control_y = np.concatenate([finite_delta, rand_delta])
    beta, *_ = np.linalg.lstsq(control_x, control_y, rcond=None)

    def resid(y: np.ndarray, x: np.ndarray) -> np.ndarray:
        return y - x @ beta

    true_resid = resid(true_delta, true_x)
    finite_resid = resid(finite_delta, finite_x)
    rand_resid = resid(rand_delta, rand_x)

    control_pred = control_x @ beta
    ss_res = float(np.sum((control_y - control_pred) ** 2))
    ss_tot = float(np.sum((control_y - float(np.mean(control_y))) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 1e-20 else 0.0
    return {
        "sigma": sigma,
        "window0": window[0],
        "window1": window[1],
        "true_delta_med": float(np.median(true_delta)),
        "finite_delta_med": float(np.median(finite_delta)),
        "random_delta_med": float(np.median(rand_delta)),
        "true_resid_med": float(np.median(true_resid)),
        "finite_resid_med": float(np.median(finite_resid)),
        "random_resid_med": float(np.median(rand_resid)),
        "true_resid_pos": float(np.mean(true_resid > 0.0)),
        "finite_resid_pos": float(np.mean(finite_resid > 0.0)),
        "random_resid_pos": float(np.mean(rand_resid > 0.0)),
        "true_minus_random_resid": float(np.median(true_resid) - np.median(rand_resid)),
        "control_r2": r2,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    print("STEP11 margin-neutralized phase-carrier control")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print(
        "sigma window true_delta finite_delta random_delta true_resid finite_resid "
        "random_resid true_resid_pos finite_resid_pos random_resid_pos "
        "true_minus_random_resid control_r2"
    )
    for window in [(100.0, 170.0), (500.0, 570.0), (14.0, 84.0)]:
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            row = summarize_case(sigma, window, args.samples, primes)
            print(
                f"{row['sigma']:.1f} [{row['window0']:.0f},{row['window1']:.0f}] "
                f"{row['true_delta_med']:+.5f} {row['finite_delta_med']:+.5f} {row['random_delta_med']:+.5f} "
                f"{row['true_resid_med']:+.5f} {row['finite_resid_med']:+.5f} {row['random_resid_med']:+.5f} "
                f"{row['true_resid_pos']:.3f} {row['finite_resid_pos']:.3f} {row['random_resid_pos']:.3f} "
                f"{row['true_minus_random_resid']:+.5f} {row['control_r2']:.3f}"
            )


if __name__ == "__main__":
    main()
