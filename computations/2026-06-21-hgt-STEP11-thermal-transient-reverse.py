#!/usr/bin/env python3
"""THE-MACHINE Step 11 for transient/steady thermal-branch metaphor.

Method #3:
    Reverse it. Instead of short transients mistaken for steady branches, test
    whether a persistent carrier band is mistaken for transient fragments when
    only short windows are inspected.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


BASE = Path(__file__).with_name("2026-06-21-hgt-STEP8-thermal-transient-ht-ghost-plateau.py")
spec = importlib.util.spec_from_file_location("ghost_ht", BASE)
ghost_ht = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(ghost_ht)


def reverse_stats(ts: np.ndarray, vals: np.ndarray, short_n: int) -> dict[str, float]:
    long_med = float(np.median(vals))
    long_pos = float(np.mean(vals > 0.04))
    persistent = int(long_med > 0.18 and long_pos > 0.70)
    short_hits = 0
    short_total = 0
    for start in range(0, len(vals) - short_n, max(1, short_n // 2)):
        seg = vals[start : start + short_n]
        short_total += 1
        short_hits += int(float(np.median(seg)) > 0.18 and float(np.mean(seg > 0.04)) > 0.70)
    miss_fraction = 1.0 - (short_hits / short_total if short_total else 0.0)
    return {
        "long_med": long_med,
        "long_pos": long_pos,
        "persistent": float(persistent),
        "short_hits": float(short_hits),
        "short_total": float(short_total),
        "miss_fraction": float(miss_fraction),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=80)
    args = parser.parse_args()

    primes = ghost_ht.first_primes(args.prime_count)
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    print("STEP11 method #3: reverse transient/steady branch metaphor")
    print("persistent criterion: long median > 0.18 and positive fraction > 0.70")
    print("kind sigma window long_med long_pos persistent short_hits short_total miss_fraction")
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            rng = np.random.default_rng(20260621 + 101 * case_index + kind_index)
            ts, vals = ghost_ht.carrier_profile(kind, sigma, window, args.samples, primes, rng)
            out = reverse_stats(ts, vals, short_n=18)
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{out['long_med']:.6f} {out['long_pos']:.6f} {out['persistent']:.0f} "
                f"{out['short_hits']:.0f} {out['short_total']:.0f} {out['miss_fraction']:.6f}"
            )
    print(
        "\nInterpretation key: if the reverse experiment only recovers the known "
        "persistent left-strip phase-defect band for true zeta, it is a useful "
        "diagnostic but not a new transient/steady theorem."
    )


if __name__ == "__main__":
    main()
