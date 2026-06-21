#!/usr/bin/env python3
"""Boundary amplification / no finite audit for source-built kappa_-.

NODE: inner-horizon mass inflation severity is controlled by surface-gravity
blueshift rate.  Tiny perturbations can be harmless at early times and dominate
later.

Transfer: even after a positive bulk and finite-rank boundary reduction, a
finite-time or finite-scale boundary audit cannot certify kappa_-=0 if boundary
channels may amplify without a uniform source bound.
"""

from __future__ import annotations

import math


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        curr = [i]
        for j, cb in enumerate(b, 1):
            curr.append(min(prev[j] + 1, curr[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = curr
    return prev[-1]


def transfer_choice() -> tuple[str, list[tuple[str, int]]]:
    node_test = (
        "Tiny initial perturbations are amplified exponentially by a rate, so "
        "finite early observations can miss later instability."
    )
    attempts = {
        "boundary_channel_rate": (
            "Tiny boundary channel couplings are amplified exponentially by a "
            "rate, so finite scale audits can miss later negative inertia."
        ),
        "static_rank_one_threshold": (
            "Fixed boundary coupling crosses a static rank-one Schur threshold "
            "and changes inertia."
        ),
        "tail_class_t0_rate": (
            "Different reciprocal near-zero tail classes give different T0 "
            "divergence rates while shifted moments stay finite."
        ),
    }
    scores = [(name, levenshtein(node_test, text)) for name, text in attempts.items()]
    scores.sort(key=lambda item: item[1])
    return scores[0][0], scores


def node_mass_inflation(epsilon: float, kappa: float, times: list[float]) -> list[dict[str, float]]:
    return [
        {
            "time": t,
            "initial_tail": epsilon,
            "surface_gravity": kappa,
            "amplified_flux": epsilon * math.exp(kappa * t),
        }
        for t in times
    ]


def neg_index(epsilon: float, rate: float, scale: float, threshold: float = 1.0) -> int:
    return int(epsilon * math.exp(rate * scale) > threshold)


def channel_crossing_time(epsilon: float, rate: float, threshold: float = 1.0) -> float:
    return math.log(threshold / epsilon) / rate


def main() -> None:
    chosen, scores = transfer_choice()
    print("Step 8 transfer attempts by Levenshtein distance")
    for name, score in scores:
        print(f"{name}: {score}")
    print(f"chosen_transfer: {chosen}")

    print()
    print("NODE small case: tiny perturbation with rate-controlled blueshift")
    for row in node_mass_inflation(1e-12, 2.0, [0.0, 5.0, 10.0, 14.0, 15.0]):
        print(row)

    print()
    print("Transferred boundary-channel model: B=I, H(t)=I-alpha(t) vv^T")
    examples = [
        {"audit_T": 10.0, "epsilon": 1e-12, "rate": 2.0},
        {"audit_T": 50.0, "epsilon": math.exp(-101.0), "rate": 2.0},
        {"audit_T": 100.0, "epsilon": math.exp(-201.0), "rate": 2.0},
    ]
    for ex in examples:
        T = ex["audit_T"]
        eps = ex["epsilon"]
        rate = ex["rate"]
        t_cross = channel_crossing_time(eps, rate)
        print(
            {
                "audit_T": T,
                "epsilon": eps,
                "rate": rate,
                "neg_at_audit": neg_index(eps, rate, T),
                "crossing_time": t_cross,
                "neg_after_crossing": neg_index(eps, rate, t_cross + 1e-6),
            }
        )

    print()
    print("Two-channel ordering can be rate-dominated, not amplitude-dominated")
    channels = [
        {"name": "large_slow", "epsilon": 1e-3, "rate": 0.5},
        {"name": "tiny_fast", "epsilon": 1e-12, "rate": 2.0},
    ]
    for ch in channels:
        print({**ch, "crossing_time": channel_crossing_time(ch["epsilon"], ch["rate"])})
    for T in [10.0, 15.0, 30.0]:
        print(
            {
                "scale": T,
                "negative_channels": [
                    ch["name"] for ch in channels if neg_index(ch["epsilon"], ch["rate"], T)
                ],
            }
        )

    print()
    print("Interpretation:")
    print(
        "The static finite-rank boundary Schur reduction is not enough for a "
        "scale-dependent source-built kappa_- experiment. For any finite audit "
        "scale T, choose epsilon < exp(-rate*T); the boundary channel has no "
        "negative direction through T but crosses the Schur threshold later. "
        "Therefore a finite-scale boundary audit cannot certify kappa_-=0 "
        "unless the completed source theorem supplies a uniform amplification "
        "bound or a scale-independent PSD boundary Weyl inequality."
    )


if __name__ == "__main__":
    main()
