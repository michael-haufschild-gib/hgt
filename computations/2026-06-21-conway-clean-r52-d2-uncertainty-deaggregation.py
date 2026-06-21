#!/usr/bin/env python3
"""Clean GPT-topic finding 52 candidate: D2 uncertainty deaggregation passport."""

from __future__ import annotations

import numpy as np


def node_hazard_uncertainty(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 200_000
    source = rng.lognormal(mean=0.0, sigma=0.55, size=n)
    motion = rng.lognormal(mean=0.0, sigma=0.70, size=n)
    risk = source * motion
    plug = np.ones(n)
    source_only = source * np.mean(motion)
    motion_only = np.mean(source) * motion

    print("NODE: source-model and ground-motion uncertainties both propagate into final risk")
    print("case mean q95 q99 exceed_3x")
    for name, arr in [
        ("plug_in", plug),
        ("source_only", source_only),
        ("motion_only", motion_only),
        ("both", risk),
    ]:
        print(
            f"{name:12s} {float(np.mean(arr)):.4f} {float(np.quantile(arr, 0.95)):.4f} "
            f"{float(np.quantile(arr, 0.99)):.4f} {float(np.mean(arr > 3.0)):.4f}"
        )
    print("constraint: a point hazard curve is not a risk estimate unless uncertainty is propagated and deaggregated")


def sample_d2(
    rng: np.random.Generator,
    trials: int,
    half_width: float,
    include_probability: float,
    measurement_sigma: float,
) -> np.ndarray:
    included = rng.random(trials) < include_probability
    measured = half_width + rng.normal(0.0, measurement_sigma, size=trials)
    measured = np.maximum(0.0, measured)
    # Symmetric off-seam pair: two positive sources at +/- measured half-width.
    return included.astype(float) * 2.0 * measured**2


def summarize_d2_case(
    rng: np.random.Generator,
    name: str,
    half_width: float,
    include_probability: float,
    measurement_sigma: float,
    threshold: float,
    trials: int = 120_000,
) -> tuple[str, float, float, float, float, float, float, float]:
    both = sample_d2(rng, trials, half_width, include_probability, measurement_sigma)
    source_only = sample_d2(rng, trials, half_width, include_probability, 0.0)
    measurement_only = sample_d2(rng, trials, half_width, 1.0, measurement_sigma)
    point = 2.0 * half_width**2
    return (
        name,
        point,
        float(np.mean(both)),
        float(np.quantile(both, 0.05)),
        float(np.quantile(both, 0.95)),
        float(np.mean(both < threshold)),
        float(np.mean(source_only < threshold)),
        float(np.mean(measurement_only < threshold)),
    )


def transfer_d2_uncertainty(seed: int = 20260622) -> None:
    rng = np.random.default_rng(seed)
    threshold = 0.0010

    print()
    print("TRANSFER: ResearchNode #7 local source-width detector D2")
    print("method #17 change representation: scalar D2 -> distribution over source and measurement models")
    print(
        "case point_D2 mean_D2 q05_D2 q95_D2 false_seam_prob "
        "source_only_false measurement_only_false"
    )
    cases = [
        ("interior_clear", 0.040, 0.995, 0.003),
        ("boundary_membership", 0.040, 0.58, 0.003),
        ("measurement_close", 0.024, 0.995, 0.010),
        ("both_uncertain", 0.024, 0.58, 0.010),
    ]
    for row in cases:
        out = summarize_d2_case(rng, *row, threshold=threshold)
        print(
            f"{out[0]:20s} {out[1]:.6f} {out[2]:.6f} {out[3]:.6f} {out[4]:.6f} "
            f"{out[5]:.3f} {out[6]:.3f} {out[7]:.3f}"
        )
    print()
    print("GATE SUMMARY")
    print(
        "near the seam, D2 should be reported as a deaggregated uncertainty distribution, "
        "not as one scalar moment"
    )
    print(
        "source-membership uncertainty and measurement/quadrature uncertainty can dominate "
        "different false-seam regimes, so guard bands alone are not a full passport"
    )


def main() -> None:
    node_hazard_uncertainty()
    transfer_d2_uncertainty()


if __name__ == "__main__":
    main()
