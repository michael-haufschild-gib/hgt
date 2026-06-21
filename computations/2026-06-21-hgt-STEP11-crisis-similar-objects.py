#!/usr/bin/env python3
"""THE-MACHINE Step 11 for crisis laminar scaling.

Method #8:
    Look for similar objects. If many nearby strip observables produce the same
    laminar-duration scaling under thresholding, the crisis analogy is generic
    run statistics rather than an HT-native constraint.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np


BASE = Path(__file__).with_name("2026-06-21-hgt-STEP8-crisis-laminar-ht-scaling.py")
spec = importlib.util.spec_from_file_location("crisis_ht", BASE)
crisis_ht = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(crisis_ht)


def observable_profile(
    observable: str,
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> np.ndarray:
    vals = []
    carrier = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = crisis_ht.gamma_part(s)
        true_p = crisis_ht.dlog_zeta(s)
        finite_p = crisis_ht.dlog_finite_euler(s, primes)
        if kind == "true":
            p = true_p
        elif kind == "finite":
            p = finite_p
        elif kind == "random-phase":
            theta = float(rng.uniform(-math.pi, math.pi))
            p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        elif kind == "gamma-only":
            p = 0.0 + 0.0j
        else:
            raise ValueError(kind)
        z = g + p
        carrier.append(z)
        if observable == "phase_defect":
            vals.append(crisis_ht.phase_defect(g, p))
        elif observable == "amplitude":
            vals.append(math.log1p(abs(z)))
        elif observable == "zero_shadow":
            vals.append(-math.log(abs(z) + 1e-300))
        elif observable == "prime_amplitude":
            vals.append(math.log1p(abs(p)))
        elif observable == "roughness":
            vals.append(0.0)
        else:
            raise ValueError(observable)
    arr = np.asarray(vals)
    if observable == "roughness":
        angles = np.unwrap(np.angle(np.asarray(carrier)))
        arr = np.abs(np.gradient(angles))
    return arr


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=320)
    parser.add_argument("--prime-count", type=int, default=80)
    args = parser.parse_args()

    primes = crisis_ht.first_primes(args.prime_count)
    quantiles = [0.55, 0.62, 0.70, 0.78, 0.86, 0.92]
    observables = ["phase_defect", "amplitude", "zero_shadow", "prime_amplitude", "roughness"]
    kinds = ["true", "finite", "random-phase", "gamma-only"]
    cases = [(0.3, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    print("STEP11 method #8: similar observables for crisis laminar scaling")
    print("kind sigma window observable alpha r2 shuffled_alpha shuffled_r2 median q90")
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            for obs_index, observable in enumerate(observables):
                rng = np.random.default_rng(20260621 + 1000 * case_index + 100 * kind_index + obs_index)
                vals = observable_profile(observable, kind, sigma, window, args.samples, primes, rng)
                out = crisis_ht.scaling(vals, quantiles)
                shuffled = vals.copy()
                rng.shuffle(shuffled)
                sh = crisis_ht.scaling(shuffled, quantiles)
                print(
                    f"{kind:13s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {observable:15s} "
                    f"{out['alpha']:.6f} {out['r2']:.6f} {sh['alpha']:.6f} {sh['r2']:.6f} "
                    f"{np.median(vals):.6f} {np.quantile(vals, 0.90):.6f}"
                )
    print(
        "\nInterpretation key: if high-R2 threshold scaling appears across many "
        "observables and survives shuffling, it is a threshold-run artifact, not "
        "a crisis-induced HT constraint."
    )


if __name__ == "__main__":
    main()
