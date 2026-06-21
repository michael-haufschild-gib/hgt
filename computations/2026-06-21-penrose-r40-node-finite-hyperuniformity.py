#!/usr/bin/env python3
"""
R40 NODE validation: finite samples can mimic hyperuniformity at sparse small k.
"""

from __future__ import annotations

import numpy as np


def structure_factor(points: np.ndarray, ks: np.ndarray) -> np.ndarray:
    vals = []
    for k in ks:
        amp = np.exp(1j * points @ k).sum()
        vals.append(abs(amp) ** 2 / len(points))
    return np.array(vals)


def main() -> None:
    rng = np.random.default_rng(4005)
    print("N   min_small_k_S  median_small_k_S  false_hyperuniform_flag")
    for n in [40, 80, 160, 320, 640]:
        pts = rng.random((n, 2))
        dirs = rng.normal(size=(12, 2))
        dirs /= np.linalg.norm(dirs, axis=1, keepdims=True)
        ks = dirs * (2 * np.pi)
        s = structure_factor(pts, ks)
        flag = int(np.min(s) < 0.05)
        print(f"{n:3d} {np.min(s):14.5f} {np.median(s):17.5f} {flag:24d}")
    print("\nNODE verdict: sparse small-k samples can produce very low S(k) outliers even for random points.")


if __name__ == "__main__":
    main()
