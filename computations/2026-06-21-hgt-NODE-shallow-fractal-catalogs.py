#!/usr/bin/env python3
"""NODE test: shallow catalogs can make apparent fractal scaling change.

NODE:
    Early fractal-cosmology arguments often relied on shallower catalogs whose
    apparent scaling could change with deeper surveys.

Constraint:
    A claimed fractal dimension from counts N(<r) is stable evidence only if it
    survives increasing the survey depth past the candidate transition scale.
"""

from __future__ import annotations

import numpy as np


SEED = 20260621
N_POINTS = 180_000
R_MAX = 1000.0
TRUE_FRACTAL_D = 2.0
TRANSITION_R = 300.0


def sample_radii(rng: np.random.Generator, model: str, n: int, d: float, r_transition: float) -> np.ndarray:
    u = rng.random(n)
    if model == "homogeneous":
        return R_MAX * u ** (1.0 / 3.0)
    if model == "pure_fractal":
        return R_MAX * u ** (1.0 / d)
    if model == "finite_fractal_to_homogeneous":
        f_transition = (r_transition / R_MAX) ** 3.0
        radii = np.empty(n, dtype=float)
        inner = u <= f_transition
        radii[inner] = r_transition * (u[inner] / max(f_transition, 1e-300)) ** (1.0 / d)
        radii[~inner] = R_MAX * u[~inner] ** (1.0 / 3.0)
        return radii
    raise ValueError(model)


def fit_dimension(radii: np.ndarray, depth: float, outer_only: bool) -> tuple[float, int]:
    observed = radii[radii <= depth]
    if observed.size < 100:
        return float("nan"), int(observed.size)
    r_min = max(12.0, depth * 0.06)
    bins = np.geomspace(r_min, depth, 24)
    counts = np.asarray([np.count_nonzero(observed <= r) for r in bins], dtype=float)
    mask = counts > 15
    if outer_only:
        outer = bins >= np.sqrt(r_min * depth)
        mask &= outer
    x = np.log(bins[mask])
    y = np.log(counts[mask])
    if x.size < 4:
        return float("nan"), int(observed.size)
    return float(np.polyfit(x, y, 1)[0]), int(observed.size)


def classify(dim: float) -> str:
    if not np.isfinite(dim):
        return "too_sparse"
    if dim < 2.35:
        return "fractal_like"
    if dim > 2.75:
        return "homogeneous_like"
    return "transition"


def summarize_model(name: str, radii: np.ndarray, depths: list[float]) -> None:
    print(f"\nMODEL {name}")
    shallow_dim = None
    deep_dim = None
    for depth in depths:
        d_all, n_obs = fit_dimension(radii, depth, outer_only=False)
        d_outer, _ = fit_dimension(radii, depth, outer_only=True)
        if depth == depths[1]:
            shallow_dim = d_outer
        if depth == depths[-1]:
            deep_dim = d_outer
        print(
            f"depth={depth:6.1f} n_obs={n_obs:6d} "
            f"D_all={d_all:6.3f} D_outer={d_outer:6.3f} "
            f"label_outer={classify(d_outer)}"
        )
    if shallow_dim is not None and deep_dim is not None:
        print(f"depth_sensitivity_outer={abs(deep_dim - shallow_dim):.3f}")


def transition_sweep(rng: np.random.Generator) -> None:
    print("\nTRANSITION SCALE SWEEP")
    print("r_transition shallow_D_outer deep_D_outer sensitivity shallow_label deep_label")
    for r_transition in [150.0, 220.0, 300.0, 450.0, 650.0]:
        radii = sample_radii(rng, "finite_fractal_to_homogeneous", N_POINTS, TRUE_FRACTAL_D, r_transition)
        shallow, _ = fit_dimension(radii, min(0.70 * r_transition, 260.0), outer_only=True)
        deep, _ = fit_dimension(radii, R_MAX, outer_only=True)
        print(
            f"{r_transition:12.1f} {shallow:15.3f} {deep:12.3f} "
            f"{abs(deep-shallow):11.3f} {classify(shallow):13s} {classify(deep):13s}"
        )


def main() -> None:
    rng = np.random.default_rng(SEED)
    depths = [90.0, 150.0, 240.0, 360.0, 520.0, 760.0, 1000.0]
    print("NODE: shallow catalog depth can change inferred fractal scaling")
    print(f"seed={SEED} n_points={N_POINTS} R_max={R_MAX} fractal_D={TRUE_FRACTAL_D} transition_R={TRANSITION_R}")
    print("criterion: finite-transition model should be depth-sensitive; pure controls should be depth-stable")

    for model in ["homogeneous", "pure_fractal", "finite_fractal_to_homogeneous"]:
        radii = sample_radii(rng, model, N_POINTS, TRUE_FRACTAL_D, TRANSITION_R)
        summarize_model(model, radii, depths)

    transition_sweep(rng)


if __name__ == "__main__":
    main()
