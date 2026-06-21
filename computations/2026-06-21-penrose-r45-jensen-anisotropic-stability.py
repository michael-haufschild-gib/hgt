#!/usr/bin/env python3
"""R45 candidate: anisotropic stability passport for Jensen/Hankel positivity.

ResearchNode 15: Uniform Jensen/Hankel.

NODE: stress-dependent diffusivity tensors caused by deformation, anisotropy,
damage, or evolving microstructure.

Transfer: a scalar positivity margin is not a tensorial stability certificate.
For Jensen hyperbolicity, the weakened local task is to measure direction-wise
distance to non-hyperbolicity in coefficient space, rather than average or
scalar-normalize the margin.
"""

from __future__ import annotations

import math
from statistics import median

import numpy as np


NODE = (
    "stress-dependent diffusivity tensors caused by deformation anisotropy "
    "damage or evolving microstructure"
)


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def gaussian_density(x: np.ndarray, diffusivity: np.ndarray, t: float) -> float:
    inv = np.linalg.inv(diffusivity)
    quad = float(x @ inv @ x)
    det = float(np.linalg.det(diffusivity))
    return math.exp(-quad / (4.0 * t)) / (4.0 * math.pi * t * math.sqrt(det))


def node_tensor_diffusion_test() -> None:
    theta = math.radians(35.0)
    rot = np.array(
        [[math.cos(theta), -math.sin(theta)], [math.sin(theta), math.cos(theta)]],
        dtype=float,
    )
    principal = np.diag([0.95, 0.08])
    tensor = rot @ principal @ rot.T
    scalar = 0.5 * float(np.trace(tensor)) * np.eye(2)
    t = 1.0
    fast_axis = rot[:, 0]
    slow_axis = rot[:, 1]
    radius = 1.0
    probes = {
        "fast_axis": radius * fast_axis,
        "slow_axis": radius * slow_axis,
        "diagonal": radius * np.array([1.0, 1.0]) / math.sqrt(2.0),
    }

    print("NODE tensor-diffusion test")
    print("same trace / same mean-square displacement, different directional flux")
    print(
        "tensor="
        f"[[{tensor[0,0]:.4f},{tensor[0,1]:+.4f}],"
        f"[{tensor[1,0]:+.4f},{tensor[1,1]:.4f}]] "
        f"scalar_D={scalar[0,0]:.4f}"
    )
    print("probe tensor_density scalar_density ratio")
    for name, probe in probes.items():
        ct = gaussian_density(probe, tensor, t)
        cs = gaussian_density(probe, scalar, t)
        print(f"{name:10s} {ct:.6e} {cs:.6e} {ct / cs:.3f}")
    print(
        "NODE verdict: scalar diffusivity preserves the trace but loses the "
        "directional constraint imposed by stress anisotropy."
    )


def xi_coefficients(max_n: int) -> list[float]:
    # Archived from computations/2026-06-21-connes-jensen-turan-apexb.txt.
    # These low-order coefficients are enough for this local stability-passport
    # experiment; recomputing the Taylor series dominates runtime and adds no
    # new evidence for the anisotropy question.
    vals = [
        0.49712077818831,
        0.01149,
        0.0001235,
        8.324e-7,
        3.992e-9,
        1.462e-11,
        4.275e-14,
        1.031e-16,
        2.100e-19,
        3.678e-22,
        5.623e-25,
        7.592e-28,
        9.143e-31,
        9.906e-34,
    ]
    if max_n >= len(vals):
        raise ValueError("precomputed coefficient table too short")
    return vals[: max_n + 1]


def jensen_coeffs(a: list[float], d: int, n: int) -> np.ndarray:
    return np.array([math.comb(d, j) * a[n + j] for j in range(d + 1)], dtype=float)


def normalized(co: np.ndarray) -> np.ndarray:
    return co / float(np.linalg.norm(co))


def hyperbolic(co: np.ndarray) -> bool:
    roots = np.roots(co[::-1])
    scale = max(1.0, float(np.max(np.abs(roots.real))))
    return bool(np.max(np.abs(roots.imag)) <= 1e-7 * scale)


def failure_radius(co: np.ndarray, direction: np.ndarray, cap: float = 1.0) -> float:
    co = normalized(co)
    direction = direction / float(np.linalg.norm(direction))

    def first_for_sign(sign: float) -> float:
        hi = 1e-8
        while hi < cap and hyperbolic(co + sign * hi * direction):
            hi *= 2.0
        if hi >= cap and hyperbolic(co + sign * cap * direction):
            return cap
        lo = 0.0
        hi = min(hi, cap)
        for _ in range(50):
            mid = 0.5 * (lo + hi)
            if hyperbolic(co + sign * mid * direction):
                lo = mid
            else:
                hi = mid
        return hi

    return min(first_for_sign(1.0), first_for_sign(-1.0))


def transfer_audit() -> None:
    attempts = [
        "jensen positivity needs an anisotropic coefficient stability tensor",
        "uniform hankel margins should use stress-dependent directional perturbations",
        "replace scalar jensen margin by direction-wise hyperbolicity radius",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #14: weaken the conjecture")
    print(
        "weakened target: not uniform-in-d positivity; only a local anisotropic "
        "coefficient-stability passport for tested Jensen polynomials"
    )

    a = xi_coefficients(13)
    rng = np.random.default_rng(4515)
    print()
    print("HGT transfer: Jensen coefficient-space anisotropy")
    print(
        "d n hyperbolic min_axis_radius median_random_radius "
        "anisotropy_ratio worst_axis"
    )
    rows = []
    for d in [3, 4]:
        for n in range(1, 8):
            co = jensen_coeffs(a, d, n)
            axes = np.eye(d + 1)
            axis_radii = [failure_radius(co, axis) for axis in axes]
            random_radii = []
            for _ in range(48):
                direction = rng.normal(size=d + 1)
                random_radii.append(failure_radius(co, direction))
            min_axis = min(axis_radii)
            med_random = float(median(random_radii))
            ratio = med_random / max(min_axis, 1e-300)
            worst_axis = int(np.argmin(axis_radii))
            rows.append((d, n, ratio, min_axis, med_random, worst_axis))
            print(
                f"{d:1d} {n:2d} {int(hyperbolic(co)):1d} "
                f"{min_axis:.6e} {med_random:.6e} {ratio:9.2f} c{worst_axis}"
            )

    high_anisotropy = sum(1 for row in rows if row[2] >= 3.0)
    tight_rows = sorted(rows, key=lambda row: row[3])[:3]
    print()
    print("Summary gates")
    print(f"high_anisotropy_rows={high_anisotropy}/{len(rows)}")
    print(
        "tightest_rows="
        + "; ".join(
            f"d={d},n={n},axis=c{axis},radius={rad:.3e},ratio={ratio:.2f}"
            for d, n, ratio, rad, _, axis in tight_rows
        )
    )
    print(
        "passport_rule=report the direction-wise hyperbolicity radius tensor; "
        "a scalar or averaged Jensen margin is not a uniform positivity certificate"
    )


def main() -> None:
    print("Penrose R45: anisotropic stability passport for Uniform Jensen/Hankel")
    print(f"NODE: {NODE}")
    node_tensor_diffusion_test()
    transfer_audit()


if __name__ == "__main__":
    main()
