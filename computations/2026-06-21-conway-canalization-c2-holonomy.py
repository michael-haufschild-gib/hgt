#!/usr/bin/env python3
"""THE-MACHINE tick: lab canalization exaggeration -> C2 holonomy.

NODE:
  Laboratory environments can exaggerate apparent canalization by removing
  ecologically relevant perturbations.

Consolidated target:
  C2 -- holonomy of the affine weld connection.

STEP 9 method:
  15. Strengthen the conjecture.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = "laboratory environments can exaggerate apparent canalization by removing ecologically relevant perturbations"

TRANSFER_ATTEMPTS = [
    "restricted lab loops can falsely trivialize C2 holonomy by removing off seam perturbations",
    "C2 holonomy needs ecological loop families not only canalized seam loops",
    "apparent holonomy canalization can be a perturbation-family artifact",
]

BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606216901)
    genotypes = rng.normal(size=(5000, 4))
    trait_base = genotypes[:, 0] + 0.25 * genotypes[:, 1] ** 2
    lab_env = rng.normal(scale=0.08, size=5000)
    eco_env = rng.normal(scale=0.55, size=5000) + 0.45 * np.sign(genotypes[:, 2])
    lab_trait = np.tanh(trait_base + lab_env)
    eco_trait = np.tanh(trait_base + eco_env)
    lines = ["STEP 6 NODE TEST: restricted environment exaggerates canalization"]
    lines.append("environment trait_variance perturbation_variance apparent_canalization")
    for name, trait, env in [("lab", lab_trait, lab_env), ("ecological", eco_trait, eco_env)]:
        trait_var = float(np.var(trait))
        env_var = float(np.var(env))
        canal = 1.0 / (trait_var + 1e-12)
        lines.append(f"{name:10s} {trait_var:.5f} {env_var:.5f} {canal:.4f}")
    lines.append(
        "NODE verdict: a narrow perturbation family makes the phenotype look more canalized than "
        "it is under ecologically relevant perturbations."
    )
    return lines


def h_value(kind: str, s: complex, primes, rng: np.random.Generator) -> complex:
    a = gamma_part(s)
    p = dlog_zeta(s)
    if kind == "true":
        return a + p
    if kind == "finite":
        return a + dlog_finite(s, primes)
    if kind == "random":
        theta = rng.uniform(-math.pi, math.pi)
        return a + abs(p) * complex(math.cos(theta), math.sin(theta))
    raise ValueError(kind)


def rectangle_points(center_sigma: float, center_t: float, ds: float, dt: float, per_edge: int = 40):
    left, right = center_sigma - ds / 2, center_sigma + ds / 2
    bottom, top = center_t - dt / 2, center_t + dt / 2
    pts = []
    for x in np.linspace(left, right, per_edge, endpoint=False):
        pts.append((x, bottom))
    for y in np.linspace(bottom, top, per_edge, endpoint=False):
        pts.append((right, y))
    for x in np.linspace(right, left, per_edge, endpoint=False):
        pts.append((x, top))
    for y in np.linspace(top, bottom, per_edge, endpoint=False):
        pts.append((left, y))
    pts.append(pts[0])
    return pts


def centered_holonomy(kind: str, pts, primes, rng) -> tuple[float, float]:
    hs = np.array([h_value(kind, complex(s, t), primes, rng) for s, t in pts])
    phi = np.unwrap(np.angle(hs))
    o = np.log1p(np.abs(hs))
    dphi = np.diff(phi)
    omid = 0.5 * (o[:-1] + o[1:])
    centered = omid - float(np.mean(omid))
    integral = float(np.sum(centered * dphi))
    winding = float((phi[-1] - phi[0]) / (2.0 * math.pi))
    return integral, winding


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Canalization variance formulas do not apply unchanged to C2. The transfer keeps the "
        "perturbation-family warning: holonomy tests must not use only restricted loop families "
        "that make the cocycle look trivial."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 15: STRENGTHEN THE CONJECTURE")
    lines.append(
        "Strengthening: use centered loop integral int (O-mean O)dphi around rectangles, not raw "
        "winding. Compare narrow lab seam loops with broader off-seam loop families."
    )

    rng = np.random.default_rng(2606217021)
    primes = first_primes(160)
    loop_families = {
        "lab_seam_narrow": [(0.50, t, 0.035, 2.0) for t in np.linspace(30, 165, 12)],
        "wide_seam": [(0.50, t, 0.18, 8.0) for t in np.linspace(35, 160, 10)],
        "offseam_wide": [(s, t, 0.16, 8.0) for s in [0.42, 0.58] for t in np.linspace(35, 160, 6)],
        "right_wide": [(1.25, t, 0.18, 8.0) for t in np.linspace(35, 160, 10)],
    }
    lines.append("family kind mean_abs_centered_hol std_centered_hol winding_nonzero_frac")
    for family, specs in loop_families.items():
        for kind in ["true", "finite", "random"]:
            vals = []
            winds = []
            for spec in specs:
                pts = rectangle_points(*spec)
                val, wind = centered_holonomy(kind, pts, primes, rng)
                vals.append(val)
                winds.append(wind)
            lines.append(
                f"{family:16s} {kind:6s} {float(np.mean(np.abs(vals))):.6f} "
                f"{float(np.std(vals)):.6f} {float(np.mean(np.abs(winds) > 0.5)):.3f}"
            )
    lines.append(
        "\nProvisional interpretation: if only narrow seam loops look trivial, C2 cannot be tested "
        "in that lab family alone. If broader true loops separate from finite/random without relying "
        "on winding, the centered holonomy is a candidate gate."
    )
    return lines


def main() -> None:
    out = []
    out.append("THE-MACHINE tick: canalization perturbation restriction -> C2 holonomy")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 10/32 C2 holonomy")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
