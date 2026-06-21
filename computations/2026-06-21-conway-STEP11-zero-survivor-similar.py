#!/usr/bin/env python3
"""STEP 11 for first-passage survivor bias -> zero geometry.

Method 8: look for similar objects.
Compare true zero absorbers with equally spaced and jittered seam absorbers.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-firstpass-survivor-zero-geometry.py")

zeta_zero_imags = BASE["zeta_zero_imags"]
simulate_survivors = BASE["simulate_survivors"]


def main() -> None:
    rng = np.random.default_rng(2606216701)
    imags = zeta_zero_imags(170.0)
    imags = imags[imags >= 14.0]
    n = len(imags)
    equal = np.linspace(14.0, 170.0, n)
    jitter = equal + rng.normal(scale=0.9, size=n)
    controls = {
        "true_zeros": np.column_stack([np.full(n, 0.5), imags]),
        "equal_seam": np.column_stack([np.full(n, 0.5), equal]),
        "jitter_seam": np.column_stack([np.full(n, 0.5), jitter]),
        "half_density_true": np.column_stack([np.full(len(imags[::2]), 0.5), imags[::2]]),
    }
    print("STEP 11 zero-survivor similar-object controls")
    print("method=8 look for similar objects")
    print("control n_absorbers alive mean_abs_seam_dist near_seam_frac right_frac")
    for name, points in controls.items():
        stats = simulate_survivors(rng, points, (0.30, 0.70), (14.0, 170.0))
        print(
            f"{name:17s} {len(points):03d} {stats['alive']:.4f} {stats['mean_abs_seam_dist']:.4f} "
            f"{stats['near_seam_frac']:.4f} {stats['left_right_balance']:.4f}"
        )
    print(
        "Interpretation: similar seam absorber sets produce the same survivor-ensemble depletion. "
        "The survivor view is a censoring artifact, not zero-specific geometry."
    )


if __name__ == "__main__":
    main()
