#!/usr/bin/env python3
"""THE-MACHINE Step 11 for inhibition-organized burst metaphor.

Method #3:
    Reverse it. Instead of inhibition organizing bursts, ask whether organized
    bursts create an apparent inhibitory shadow afterward. If this appears in
    finite/random controls too, it is generic threshold-aftereffect geometry.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


BASE = Path(__file__).with_name("2026-06-21-hgt-STEP8-inhibition-phase-bursts.py")
spec = importlib.util.spec_from_file_location("inhib_ht", BASE)
inhib_ht = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(inhib_ht)


def burst_shadow(vals: np.ndarray, gap: int = 6) -> dict[str, float]:
    threshold = float(np.quantile(vals, 0.82))
    burst_idx = np.flatnonzero(vals > threshold)
    pre = []
    post = []
    for idx in burst_idx:
        if idx - gap >= 0 and idx + gap < len(vals):
            pre.append(float(np.mean(vals[idx - gap : idx])))
            post.append(float(np.mean(vals[idx + 1 : idx + 1 + gap])))
    if not pre:
        return {"n": 0.0, "pre": 0.0, "post": 0.0, "shadow": 0.0, "shadow_frac": 0.0}
    pre_a = np.asarray(pre)
    post_a = np.asarray(post)
    shadow = pre_a - post_a
    return {
        "n": float(len(pre)),
        "pre": float(np.median(pre_a)),
        "post": float(np.median(post_a)),
        "shadow": float(np.median(shadow)),
        "shadow_frac": float(np.mean(shadow > 0.0)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=80)
    args = parser.parse_args()

    primes = inhib_ht.first_primes(args.prime_count)
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    print("STEP11 method #3: reverse inhibition/burst metaphor")
    print("test: do high phase-bursts create an apparent post-burst inhibitory shadow?")
    print("kind sigma window n_bursts pre_median post_median shadow_median shadow_positive_fraction")
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            rng = np.random.default_rng(20260621 + 101 * case_index + kind_index)
            vals = inhib_ht.profile(kind, sigma, window, args.samples, primes, rng)
            out = burst_shadow(vals)
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{out['n']:.0f} {out['pre']:.6f} {out['post']:.6f} "
                f"{out['shadow']:.6f} {out['shadow_frac']:.6f}"
            )
    print(
        "\nInterpretation key: a true-only positive post-burst shadow would be "
        "interesting; broad occurrence in finite/random/right-side controls "
        "means generic threshold aftereffect."
    )


if __name__ == "__main__":
    main()
