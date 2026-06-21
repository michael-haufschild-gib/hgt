#!/usr/bin/env python3
"""STEP 11 control for Palm reference -> zero geometry.

Question:
  Is the reduced-Palm signal a source-geometry feature, or is it reproduced by
  simple spacing regularity after removing the Palm self-atom?
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-palm-reference-zero-geometry.py")
zeta_zero_imags = BASE["zeta_zero_imags"]
gaussian_kernel_stats = BASE["gaussian_kernel_stats"]


def jittered_lattice(window, n, jitter_frac, rng):
    spacing = (window[1] - window[0]) / (n + 1)
    base = np.linspace(window[0], window[1], n + 2)[1:-1]
    jitter = rng.normal(scale=jitter_frac * spacing, size=n)
    out = np.clip(base + jitter, window[0], window[1])
    return np.sort(out)


def main() -> None:
    rng = np.random.default_rng(2606216109)
    zeros = zeta_zero_imags(720.0)
    cases = [
        ("low", (14.0, 170.0), 0.40),
        ("mid", (170.0, 360.0), 0.35),
        ("high", (360.0, 720.0), 0.30),
    ]
    jitters = [0.00, 0.03, 0.06, 0.10, 0.16, 0.25, 0.40]
    print("STEP 11 Palm reduced-self jitter control")
    print("case true_ratio best_jitter best_ratio abs_diff ratios_by_jitter verdict")
    matched = 0
    for label, window, bw in cases:
        z = zeros[(zeros >= window[0]) & (zeros <= window[1])]
        ordinary, _palm, reduced = gaussian_kernel_stats(z, window, bw)
        true_ratio = reduced / (ordinary + 1e-300)
        ratios = []
        for jf in jitters:
            vals = []
            for _ in range(12):
                pts = jittered_lattice(window, len(z), jf, rng)
                o, _p, r = gaussian_kernel_stats(pts, window, bw)
                vals.append(r / (o + 1e-300))
            ratios.append(float(np.mean(vals)))
        diffs = [abs(v - true_ratio) for v in ratios]
        idx = int(np.argmin(diffs))
        ok = diffs[idx] < 0.06
        matched += int(ok)
        ratio_str = ",".join(f"{jf:.2f}:{v:.3f}" for jf, v in zip(jitters, ratios))
        print(
            f"{label:5s} {true_ratio:.4f} {jitters[idx]:.2f} {ratios[idx]:.4f} "
            f"{diffs[idx]:.4f} [{ratio_str}] {int(ok)}"
        )
    print()
    print(f"TRUE_REDUCED_PALM_MATCHED_BY_JITTERED_LATTICE {matched}/{len(cases)}")
    print(
        "Interpretation: matching by lightly jittered lattice controls means the reduced-Palm "
        "signal is spacing regularity/repulsion after self-atom removal, not new source-location "
        "geometry."
    )


if __name__ == "__main__":
    main()
