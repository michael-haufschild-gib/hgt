#!/usr/bin/env python3
"""THE-MACHINE Step 11 for prion-like mixing-order path dependence.

Metaphor:
    The NODE says a final composition does not determine material state; the
    path through assembly space matters. For "constraint, not flow", the wild
    HT analogue asks where an order/pathway constraint can be seen after the
    same final continuum components are present.

Method #23:
    Classify boundary cases: no aging, defect ablated, roughness ablated,
    saturated roughness, right strip, finite/random controls.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


BASE = Path(__file__).with_name("2026-06-21-hgt-STEP8-prion-mixing-order-ht-pathway.py")
spec = importlib.util.spec_from_file_location("mixing_ht", BASE)
mixing_ht = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(mixing_ht)


def spread_for_components(components: dict[str, np.ndarray], age_steps: int) -> tuple[float, str, str]:
    vectors = []
    labels = []
    for order in mixing_ht.itertools.permutations(mixing_ht.COMPONENTS):
        vectors.append(mixing_ht.run_order(components, order, age_steps=age_steps))
        labels.append("-".join(order))
    arr = np.asarray(vectors)
    pairwise = [
        float(np.linalg.norm(arr[i] - arr[j], ord=1))
        for i in range(len(arr))
        for j in range(i + 1, len(arr))
    ]
    score = arr[:, 1] + arr[:, 2]
    return max(pairwise) if pairwise else 0.0, labels[int(np.argmax(score))], labels[int(np.argmin(score))]


def boundary_case(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    mode: str,
    age_steps: int,
    seed: int,
) -> tuple[float, float, str, str]:
    rng = np.random.default_rng(seed)
    defect, amplitude, roughness = mixing_ht.carrier_values(kind, sigma, window, samples, primes, rng)
    if mode == "full":
        components = {"protein": defect, "rna": amplitude, "salt": roughness}
    elif mode == "no_defect":
        components = {"protein": np.zeros_like(defect), "rna": amplitude, "salt": roughness}
    elif mode == "defect_only":
        components = {"protein": defect, "rna": np.ones_like(amplitude), "salt": np.zeros_like(roughness)}
    elif mode == "no_roughness":
        components = {"protein": defect, "rna": amplitude, "salt": np.zeros_like(roughness)}
    elif mode == "saturated_roughness":
        components = {"protein": defect, "rna": amplitude, "salt": np.ones_like(roughness)}
    elif mode == "shuffled_defect":
        shuffled = defect.copy()
        rng.shuffle(shuffled)
        components = {"protein": shuffled, "rna": amplitude, "salt": roughness}
    else:
        raise ValueError(mode)
    spread, best, worst = spread_for_components(components, age_steps=age_steps)
    return float(np.median(defect)), spread, best, worst


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    primes = mixing_ht.first_primes(args.prime_count)
    print("STEP11 method #23: classify boundary cases for path/mixing-order memory")
    print("boundary_signal threshold: max_order_spread >= 0.002")
    print("kind sigma window mode age_steps defect_med max_order_spread signal best_order worst_order")

    cases = [
        ("true", 0.3, (100.0, 170.0)),
        ("true", 0.3, (500.0, 570.0)),
        ("true", 0.5, (100.0, 170.0)),
        ("true", 0.7, (100.0, 170.0)),
        ("true", 1.2, (100.0, 170.0)),
        ("finite", 0.3, (100.0, 170.0)),
        ("ampmatched-finite", 0.3, (100.0, 170.0)),
        ("random-phase", 0.3, (100.0, 170.0)),
    ]
    modes = ["full", "no_defect", "defect_only", "no_roughness", "saturated_roughness", "shuffled_defect"]
    age_steps_list = [0, 2, 8, 16]
    for idx, (kind, sigma, window) in enumerate(cases):
        for mode in modes:
            for age_steps in age_steps_list:
                defect_med, spread, best, worst = boundary_case(
                    kind,
                    sigma,
                    window,
                    args.samples,
                    primes,
                    mode,
                    age_steps,
                    seed=20260622 + idx * 101 + age_steps,
                )
                signal = int(spread >= 0.002)
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{mode:19s} {age_steps:2d} {defect_med:.6f} {spread:.6f} "
                    f"{signal:d} {best} {worst}"
                )

    print(
        "\nInterpretation key: if the boundary classifier says order-memory is "
        "present exactly when the defect component is present, age/nonlinearity "
        "is nonzero, and sigma is left-of-one, then the metaphor experiment "
        "confirms reduction to the existing phase-carrier defect rather than a "
        "new path-dependence invariant."
    )


if __name__ == "__main__":
    main()
