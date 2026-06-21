#!/usr/bin/env python3
"""THE-MACHINE tick: Palm reference measure -> zero geometry.

NODE:
  Palm expectations depend on the reference measure, typically the intensity
  measure of the point process.

Consolidated target:
  6/32 Where the zeros live in the geometry.

STEP 9 method:
  12. Find an invariant.
"""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


NODE = "Palm expectations depend on the reference measure, typically the intensity measure of the point process"
TARGET = "6/32 Where the zeros live in the geometry"
METHOD = "12. Find an invariant"

TRANSFER_ATTEMPTS = [
    "zero source geometry must state whether expectation is height uniform or source Palm",
    "Palm reference measure becomes source measure reference for zero geometry",
    "typical zero statistics are size biased unless Campbell inverted to height statistics",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606215921)
    n = 250000
    x = rng.uniform(size=n)
    weights_left = 0.4 + 3.2 * (1.0 - x)
    weights_right = 0.4 + 3.2 * x
    ordinary_mean = float(np.mean(x))
    palm_left = float(np.sum(x * weights_left) / np.sum(weights_left))
    palm_right = float(np.sum(x * weights_right) / np.sum(weights_right))
    palm_quad_left = float(np.sum((x - 0.5) ** 2 * weights_left) / np.sum(weights_left))
    palm_quad_right = float(np.sum((x - 0.5) ** 2 * weights_right) / np.sum(weights_right))
    lines = ["STEP 5/6 NODE TEST: Palm expectations need the reference measure"]
    lines.append(
        "Constraint: a typical point is sampled through the intensity/reference measure, not "
        "through uniform location sampling."
    )
    lines.append("reference ordinary_E_x palm_E_x palm_E_centered_square")
    lines.append(f"uniform {ordinary_mean:.6f} {ordinary_mean:.6f} {float(np.mean((x-0.5)**2)):.6f}")
    lines.append(f"left_weight {ordinary_mean:.6f} {palm_left:.6f} {palm_quad_left:.6f}")
    lines.append(f"right_weight {ordinary_mean:.6f} {palm_right:.6f} {palm_quad_right:.6f}")
    lines.append(
        "NODE verdict: the same cloud has different Palm expectations when the reference "
        "measure changes. Palm claims without a reference measure are under-specified."
    )
    return lines


def zeta_zero_imags(max_t: float) -> np.ndarray:
    vals = []
    k = 1
    while True:
        z = complex(mp.zetazero(k))
        if z.imag > max_t:
            break
        vals.append(float(z.imag))
        k += 1
    return np.asarray(vals, dtype=float)


def gaussian_kernel_stats(points: np.ndarray, window: tuple[float, float], bandwidth: float) -> tuple[float, float, float]:
    grid = np.linspace(window[0], window[1], 4000)
    diff = (grid[:, None] - points[None, :]) / bandwidth
    k_grid = np.exp(-0.5 * diff * diff)
    ordinary = float(np.mean(np.sum(k_grid, axis=1)))
    pdiff = (points[:, None] - points[None, :]) / bandwidth
    k_palm = np.exp(-0.5 * pdiff * pdiff)
    palm = float(np.mean(np.sum(k_palm, axis=1)))
    reduced = float(np.mean(np.sum(k_palm, axis=1) - 1.0))
    return ordinary, palm, reduced


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Palm formulas do not apply unchanged to zeros: zero source measure is deterministic "
        "in this experiment and conditioning on a zero is zero-feeding unless declared."
    )
    lines.append(
        "Minimal transfer: audit whether a zero-geometry statistic is height-uniform, "
        "source-Palm, or reduced-Palm/Campbell corrected."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 12: FIND AN INVARIANT")
    lines.append(
        "Invariant sought: after subtracting the Palm self-atom and comparing to same-count "
        "reference processes, any remaining source-neighborhood signal should not be universal "
        "simple-point bias."
    )

    rng = np.random.default_rng(2606216001)
    all_zeros = zeta_zero_imags(720.0)
    cases = [
        ("low", (14.0, 170.0), 0.40),
        ("mid", (170.0, 360.0), 0.35),
        ("high", (360.0, 720.0), 0.30),
    ]
    lines.append("case model n bandwidth ordinary palm reduced palm_over_ord reduced_over_ord")
    fake_matches = 0
    total = 0
    for label, window, bw in cases:
        z = all_zeros[(all_zeros >= window[0]) & (all_zeros <= window[1])]
        n = len(z)
        poisson = np.sort(rng.uniform(window[0], window[1], size=n))
        lattice = np.linspace(window[0], window[1], n + 2)[1:-1]
        models = {"true_zero": z, "poisson_same_n": poisson, "lattice_same_n": lattice}
        vals = {}
        for name, points in models.items():
            ordinary, palm, reduced = gaussian_kernel_stats(points, window, bw)
            vals[name] = (ordinary, palm, reduced)
            lines.append(
                f"{label:5s} {name:14s} {n:03d} {bw:.2f} {ordinary:.6f} {palm:.6f} "
                f"{reduced:.6f} {palm/(ordinary+1e-300):.4f} {reduced/(ordinary+1e-300):.4f}"
            )
        true_ratio = vals["true_zero"][2] / (vals["true_zero"][0] + 1e-300)
        ctrl_ratio = max(
            vals["poisson_same_n"][2] / (vals["poisson_same_n"][0] + 1e-300),
            vals["lattice_same_n"][2] / (vals["lattice_same_n"][0] + 1e-300),
        )
        fake_matches += int(abs(true_ratio - ctrl_ratio) < 0.20)
        total += 1
    lines.append("")
    lines.append(f"REDUCED_PALM_TRUE_MATCHED_BY_CONTROLS {fake_matches}/{total}")
    lines.append(
        "Interpretation: if same-count Poisson/lattice controls reproduce the Palm/reduced-Palm "
        "ratios, this is a reference-measure warning, not new zero geometry. The source measure "
        "must be declared, and Palm self-atoms must be subtracted before promoting local-zero "
        "statistics."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: Palm reference measure -> zero geometry")
    out.append(f"NODE: {NODE}")
    out.append(f"Standing-order target: {TARGET}")
    out.append(f"STEP 9 method: {METHOD}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
