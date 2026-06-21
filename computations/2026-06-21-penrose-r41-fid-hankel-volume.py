#!/usr/bin/env python3
"""
R41 STEP 8/9 transfer to FID positivity.

NODE: determinants are squared volumes; near-linear dependence suppresses joint probability.
Target: FID positivity via free-cumulant/Hankel forms.

Method #13: find a monotone quantity.
"""

from __future__ import annotations

import mpmath as mp
import numpy as np

mp.mp.dps = 80


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(min(prev[j] + 1, row[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = row
    return prev[-1]


def kappa(n: int) -> float:
    # Corpus experimental proxy: free cumulants kappa_n = zeta(2n+1).
    return float(mp.zeta(2 * n + 1))


def hankel(size: int, perturb: tuple[int, float] | None = None) -> np.ndarray:
    vals = {i: kappa(i) for i in range(1, 2 * size + 1)}
    if perturb is not None:
        idx, delta = perturb
        vals[idx] = vals.get(idx, kappa(idx)) + delta
    return np.array([[vals[i + j + 1] for j in range(size)] for i in range(size)], dtype=float)


def main() -> None:
    source = "determinant_squared_volume_near_linear_dependence"
    attempts = [
        "fid_hankel_volume_near_dependence",
        "free_cumulant_determinant_suppression",
        "fid_positive_cone_volume_bottleneck",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:44s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    print("\nSTEP 9 method 13: monotone Hankel-volume collapse")
    print("size  min_eig        max_eig        log10_det    cond        rel_gap")
    for size in range(2, 9):
        h = hankel(size)
        eig = np.linalg.eigvalsh(h)
        sign, logdet = np.linalg.slogdet(h)
        rel_gap = eig[0] / eig[-1]
        print(
            f"{size:4d} {eig[0]:13.6g} {eig[-1]:13.6g} {logdet/np.log(10):11.4f} "
            f"{eig[-1]/eig[0]:10.3e} {rel_gap:12.3e}"
        )

    print("\nPerturb kappa_3 downward until PSD fails")
    print("size  base_min_eig  delta_k3_failure")
    for size in [3, 4, 5, 6]:
        base = np.linalg.eigvalsh(hankel(size))[0]
        lo, hi = -1.0, 0.0
        for _ in range(50):
            mid = 0.5 * (lo + hi)
            mn = np.linalg.eigvalsh(hankel(size, perturb=(3, mid)))[0]
            if mn < 0:
                lo = mid
            else:
                hi = mid
        print(f"{size:4d} {base:13.6g} {hi:17.10g}")

    print(
        "\nInterpretation: the zeta-odd cumulant Hankel forms stay positive in these sizes, "
        "but their determinant volume collapses rapidly because the sequence tends to 1. "
        "FID positivity lives close to a rank-one boundary."
    )


if __name__ == "__main__":
    main()
