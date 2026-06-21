#!/usr/bin/env python3
"""R50 candidate: objectwise compatibility passport for native weld category M+.

ResearchNode 21: native weld category M+.

NODE: basin boundaries can be crossed by fluctuations long before mean behavior
changes.

Transfer: an averaged Gamma/prime compatibility defect is not a categorical
weld.  M+ needs objectwise/fiberwise commutation data; mean-zero defects can
hide rare objects that have already crossed the compatibility boundary.
"""

from __future__ import annotations

import math

import numpy as np


NODE = "boundaries of basins of attraction may be crossed by fluctuations long before mean behavior changes"


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_basin_crossing(seed: int = 5021) -> None:
    rng = np.random.default_rng(seed)
    n = 5000
    dt = 0.005
    steps = int(8.0 / dt)
    sigma = 0.45
    x = np.full(n, -1.0)
    crossed = np.zeros(n, dtype=bool)
    for _ in range(steps):
        x += (x - x**3) * dt + sigma * math.sqrt(dt) * rng.normal(size=n)
        crossed |= x > 0.0
    print("NODE noise-induced basin crossing test")
    print(
        f"sigma={sigma:.2f} ever_crossed_rate={np.mean(crossed):.3f} "
        f"final_positive_rate={np.mean(x > 0):.3f} mean_final_x={np.mean(x):+.6f} "
        f"median_final_x={np.median(x):+.6f}"
    )
    print(
        "NODE verdict: many paths cross the basin boundary while the mean "
        "state remains in the original basin."
    )


def commutator(a: np.ndarray, p: np.ndarray) -> np.ndarray:
    return a @ p - p @ a


def transfer_audit() -> None:
    attempts = [
        "M+ needs objectwise Gamma-prime compatibility not ensemble mean commutation",
        "weld category boundary crossings hide under averaged commutator defects",
        "change viewpoint from mean weld residual to fiberwise naturality squares",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #4: change the viewpoint")
    print("from ensemble-mean compatibility to objectwise/fiberwise naturality squares")

    rng = np.random.default_rng(5022)
    n = 5000
    arch = np.array([[0.0, 1.0], [0.0, 0.0]])
    rare = rng.random(n) < 0.055
    signs = rng.choice([-1.0, 1.0], size=n)
    eps = rng.normal(0.0, 0.008, size=n)
    eps[rare] += signs[rare] * rng.uniform(0.28, 0.44, size=int(np.sum(rare)))
    prime_ops = np.array([[[0.0, 0.0], [e, 0.0]] for e in eps])
    comms = np.array([commutator(arch, p) for p in prime_ops])
    norms = np.linalg.norm(comms.reshape(n, -1), axis=1)
    mean_prime = np.mean(prime_ops, axis=0)
    mean_comm_norm = float(np.linalg.norm(commutator(arch, mean_prime)))
    mean_of_norms = float(np.mean(norms))
    threshold = 0.25

    control_eps = rng.normal(0.0, 0.008, size=n)
    control_ops = np.array([[[0.0, 0.0], [e, 0.0]] for e in control_eps])
    control_norms = np.linalg.norm(
        np.array([commutator(arch, p) for p in control_ops]).reshape(n, -1),
        axis=1,
    )
    control_mean_comm_norm = float(np.linalg.norm(commutator(arch, np.mean(control_ops, axis=0))))

    print()
    print("HGT transfer: objectwise weld-compatibility audit")
    print("family mean_comm_norm mean_object_norm p95_object_norm boundary_cross_rate median_object_norm")
    print(
        f"rare_balanced {mean_comm_norm:.6e} {mean_of_norms:.6e} "
        f"{np.quantile(norms, 0.95):.6e} {np.mean(norms > threshold):.3f} "
        f"{np.median(norms):.6e}"
    )
    print(
        f"small_control {control_mean_comm_norm:.6e} {np.mean(control_norms):.6e} "
        f"{np.quantile(control_norms, 0.95):.6e} {np.mean(control_norms > threshold):.3f} "
        f"{np.median(control_norms):.6e}"
    )
    print(
        "passport_rule=M+ compatibility must be certified objectwise or by a "
        "tail bound; ensemble-zero Gamma/prime commutator is not a weld"
    )


def main() -> None:
    print("Penrose R50: objectwise compatibility passport for native weld category M+")
    print(f"NODE: {NODE}")
    node_basin_crossing()
    transfer_audit()


if __name__ == "__main__":
    main()
