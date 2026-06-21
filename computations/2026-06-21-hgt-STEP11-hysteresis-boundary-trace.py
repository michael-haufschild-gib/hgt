#!/usr/bin/env python3
"""THE-MACHINE Step 11 for major-loop/minor-loop hysteresis metaphor.

Metaphor:
    A major hysteresis loop is only a boundary trace; minor loops reveal hidden
    memory. For HT, test whether boundary sigma traces determine interior strip
    phase-carrier behavior.

Method #23:
    Classify boundary cases for a boundary-trace predictor across function
    controls, windows, and interior sigma lanes.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import mpmath as mp
import numpy as np


BASE = Path(__file__).with_name("2026-06-21-hgt-STEP8-hysteresis-major-loop-ht-minors.py")
spec = importlib.util.spec_from_file_location("hyst_ht", BASE)
hyst_ht = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(hyst_ht)


def observable(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = hyst_ht.gamma_part(s)
        true_p = hyst_ht.dlog_zeta(s)
        finite_p = hyst_ht.dlog_finite_euler(s, primes)
        if kind == "true":
            p = true_p
        elif kind == "finite":
            p = finite_p
        elif kind == "ampmatched-finite":
            p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
        elif kind == "random-phase":
            theta = float(rng.uniform(-math.pi, math.pi))
            p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        elif kind == "gamma-only":
            p = 0.0 + 0.0j
        else:
            raise ValueError(kind)
        vals.append(hyst_ht.phase_defect(g, p))
    return np.asarray(vals)


def boundary_predict(left: np.ndarray, right: np.ndarray, sigma: float, left_sigma: float, right_sigma: float) -> np.ndarray:
    w = (sigma - left_sigma) / (right_sigma - left_sigma)
    return (1.0 - w) * left + w * right


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=90)
    parser.add_argument("--prime-count", type=int, default=80)
    args = parser.parse_args()

    primes = hyst_ht.first_primes(args.prime_count)
    rng = np.random.default_rng(20260621)
    left_sigma = 0.15
    right_sigma = 1.20
    interiors = [0.30, 0.50, 0.70, 0.95]
    windows = [(14.0, 54.0), (100.0, 140.0), (500.0, 540.0)]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]

    print("STEP11 method #23: classify boundary-trace failure cases")
    print("boundary traces: sigma=0.15 and sigma=1.20; interior lanes predicted by linear boundary interpolation")
    print("signal threshold: median_abs_error >= 0.05")
    print("kind window sigma actual_med pred_med median_abs_error q90_abs_error signal")
    for window in windows:
        for kind in kinds:
            left = observable(kind, left_sigma, window, args.samples, primes, rng)
            right = observable(kind, right_sigma, window, args.samples, primes, rng)
            for sigma in interiors:
                actual = observable(kind, sigma, window, args.samples, primes, rng)
                pred = boundary_predict(left, right, sigma, left_sigma, right_sigma)
                err = np.abs(actual - pred)
                signal = int(float(np.median(err)) >= 0.05)
                print(
                    f"{kind:17s} [{window[0]:.0f},{window[1]:.0f}] {sigma:.2f} "
                    f"{np.median(actual):.6f} {np.median(pred):.6f} "
                    f"{np.median(err):.6f} {np.quantile(err, 0.90):.6f} {signal:d}"
                )

    print(
        "\nInterpretation key: if boundary-trace failure appears only for true "
        "left/interior lanes and disappears for controls or right lanes, the "
        "metaphor again reduces to the existing left-strip phase-defect signal."
    )


if __name__ == "__main__":
    main()
