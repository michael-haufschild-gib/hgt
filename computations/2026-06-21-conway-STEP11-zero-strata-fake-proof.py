#!/usr/bin/env python3
"""STEP 11 fake-proof gap for enhanced-symmetry zero strata."""

from __future__ import annotations

import math

import numpy as np


def circle_points(center: complex, radius: float, n: int = 96) -> list[complex]:
    return [center + radius * complex(math.cos(2 * math.pi * j / n), math.sin(2 * math.pi * j / n)) for j in range(n)]


def fake_h(s: complex, zeros: list[complex]) -> complex:
    return sum(1 / (s - z) for z in zeros)


def isotropy(center: complex, zeros: list[complex], radius: float) -> tuple[float, float]:
    vals = [abs((p - center) * fake_h(p, zeros)) for p in circle_points(center, radius)]
    arr = np.array(vals, dtype=float)
    return float(np.mean(arr)), float(np.std(arr) / (np.mean(arr) + 1e-300))


def main() -> None:
    rng = np.random.default_rng(2606212336)
    print("STEP 11 METHOD 19: WRITE THE FAKE PROOF")
    print("Fake proof: zeros are enhanced symmetry strata because local source count is 1 and (s-rho) dlog f is almost isotropic.")
    print("Gap test: arbitrary simple-zero meromorphic controls should satisfy the same local test.")
    print("control zero radius mean cv verdict")
    for control in ["lattice", "random"]:
        if control == "lattice":
            zeros = [complex(0.5, 20 + 4 * k) for k in range(8)]
        else:
            zeros = [complex(0.5 + rng.normal(0, 0.03), 20 + 4 * k + rng.normal(0, 0.4)) for k in range(8)]
        for idx, z in enumerate(zeros[:4], 1):
            for radius in [0.01, 0.03, 0.08, 0.16]:
                mean, cv = isotropy(z, zeros, radius)
                verdict = "passes-local-pole-test" if abs(mean - 1) < 0.02 and cv < 0.12 else "background-visible"
                print(f"{control:7s} {idx:02d} {radius:.2f} {mean:.6f} {cv:.6f} {verdict}")
    print()
    print(
        "Conclusion: the proof proves only the universal simple-pole normal form. "
        "It does not identify the zeta zero geometry beyond source-count/local-pole facts."
    )


if __name__ == "__main__":
    main()
