#!/usr/bin/env python3
"""NODE test: redshift-space distortions alter inferred clustering dimension.

NODE:
    Redshift-space distortions from peculiar velocities can stretch or compress
    structures and alter inferred clustering dimensions.

Constraint:
    A clustering/fractal dimension inferred from redshift coordinates is valid
    only after the line-of-sight velocity distortion has been modeled or
    controlled. The same real-space catalog can yield different dimensions.
"""

from __future__ import annotations

import numpy as np


SEED = 20260621
N_CENTERS = 70
POINTS_PER_CENTER = 70
N_PAIRS = 260_000


def generate_catalog(rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray]:
    centers = rng.uniform(-1.0, 1.0, size=(N_CENTERS, 3))
    labels = np.repeat(np.arange(N_CENTERS), POINTS_PER_CENTER)
    pts = np.repeat(centers, POINTS_PER_CENTER, axis=0)
    pts += rng.normal(0.0, 0.055, size=pts.shape)
    return pts, labels


def distort_catalog(rng: np.random.Generator, pts: np.ndarray, labels: np.ndarray, mode: str, strength: float) -> np.ndarray:
    out = pts.copy()
    if mode == "finger":
        center_velocity = rng.normal(0.0, strength, size=N_CENTERS)
        internal_velocity = rng.normal(0.0, 0.35 * strength, size=len(pts))
        out[:, 2] += center_velocity[labels] + internal_velocity
    elif mode == "compression":
        out[:, 2] *= 1.0 - strength
    elif mode == "mixed":
        center_velocity = rng.normal(0.0, strength, size=N_CENTERS)
        out[:, 2] = (1.0 - 0.55 * strength) * out[:, 2] + center_velocity[labels]
    else:
        raise ValueError(mode)
    return out


def sample_distances(rng: np.random.Generator, pts: np.ndarray) -> np.ndarray:
    n = len(pts)
    i = rng.integers(0, n, size=N_PAIRS)
    j = rng.integers(0, n, size=N_PAIRS)
    mask = i != j
    d = np.linalg.norm(pts[i[mask]] - pts[j[mask]], axis=1)
    return d[d > 1e-12]


def estimate_dimension(distances: np.ndarray) -> tuple[float, float, float]:
    radii = np.geomspace(0.035, 0.75, 26)
    counts = np.asarray([np.mean(distances < r) for r in radii], dtype=float)
    mask = (counts > 0.015) & (counts < 0.45)
    x = np.log(radii[mask])
    y = np.log(counts[mask])
    slope = float(np.polyfit(x, y, 1)[0])
    fit = np.polyval(np.polyfit(x, y, 1), x)
    ss_res = float(np.sum((y - fit) ** 2))
    ss_tot = float(np.sum((y - np.mean(y)) ** 2))
    r2 = 1.0 - ss_res / max(ss_tot, 1e-12)
    return slope, r2, float(np.median(distances))


def anisotropy(pts: np.ndarray) -> float:
    cov = np.cov(pts.T)
    xy = 0.5 * (cov[0, 0] + cov[1, 1])
    return float(cov[2, 2] / max(xy, 1e-12))


def print_case(name: str, rng: np.random.Generator, pts: np.ndarray) -> tuple[float, float]:
    distances = sample_distances(rng, pts)
    dim, r2, med = estimate_dimension(distances)
    aniso = anisotropy(pts)
    print(f"{name:22s} D_hat={dim:.4f} r2={r2:.4f} median_pair={med:.4f} z_xy_aniso={aniso:.4f}")
    return dim, aniso


def main() -> None:
    rng = np.random.default_rng(SEED)
    pts, labels = generate_catalog(rng)
    print("NODE: redshift-space distortion changes inferred clustering dimension")
    print(f"seed={SEED} n_points={len(pts)} n_pairs={N_PAIRS}")
    real_dim, _ = print_case("real_space", rng, pts)
    for mode in ["finger", "compression", "mixed"]:
        for strength in [0.08, 0.16, 0.28, 0.42]:
            distorted = distort_catalog(rng, pts, labels, mode, strength)
            dim, aniso = print_case(f"{mode}_{strength:.2f}", rng, distorted)
            print(f"DELTA mode={mode} strength={strength:.2f} delta_D={dim-real_dim:+.4f} aniso={aniso:.4f}")
    print("\ncriterion")
    print("If D_hat changes while the real-space catalog is fixed, the dimension estimate is conditional on redshift-space distortion modeling.")


if __name__ == "__main__":
    main()
