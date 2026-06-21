#!/usr/bin/env python3
"""STEP 12 stress battery for SOC timescale separation -> C4."""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-soc-timescale-c4.py")

first_primes = BASE["first_primes"]
build_fields = BASE["build_fields"]
temporal_close = BASE["temporal_close"]
component_metrics = BASE["component_metrics"]


def row_metrics(fields, threshold, gap):
    out = {}
    for kind in ["true", "finite", "random"]:
        ev = temporal_close(fields[kind] > threshold, gap)
        out[kind] = component_metrics(ev)
        out[kind]["event_fraction"] = float(np.mean(ev))
    return out


def main() -> None:
    rng = np.random.default_rng(2606212507)
    primes = first_primes(160)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    windows = [(14.0, 84.0), (100.0, 170.0), (260.0, 330.0), (500.0, 570.0)]
    qs = [0.70, 0.78, 0.85]
    gaps = [0, 4, 8, 16]
    print("STEP 12 SOC/C4 event-resolution battery")
    print("samples=360 sigmas=7 finite_primes=160")
    print(
        "window q gap true_span finite_span random_span true_area finite_area random_area "
        "true_count finite_count random_count resolution_gate"
    )
    survive = 0
    trials = 0
    false_random_after_gap = 0
    for window in windows:
        fields = build_fields(sigmas, window, 360, primes, rng)
        for q in qs:
            threshold = float(np.quantile(fields["true"], q))
            base = row_metrics(fields, threshold, 0)
            base_ok = (
                base["true"]["max_sigma_span"] == 7
                and base["true"]["max_area"] > 1.7 * max(base["finite"]["max_area"], 1.0)
                and base["true"]["max_area"] > 5.0 * max(base["random"]["max_area"], 1.0)
            )
            for gap in gaps:
                m = row_metrics(fields, threshold, gap)
                random_false = m["random"]["max_sigma_span"] == 7 and gap > 0
                false_random_after_gap += int(random_false)
                gate = int(base_ok and (gap == 0 or random_false or m["finite"]["max_area"] > base["finite"]["max_area"]))
                if gap == 0:
                    survive += int(base_ok)
                    trials += 1
                print(
                    f"[{window[0]:.0f},{window[1]:.0f}] {q:.2f} {gap:02d} "
                    f"{m['true']['max_sigma_span']:.0f} {m['finite']['max_sigma_span']:.0f} {m['random']['max_sigma_span']:.0f} "
                    f"{m['true']['max_area']:.0f} {m['finite']['max_area']:.0f} {m['random']['max_area']:.0f} "
                    f"{m['true']['count']:.0f} {m['finite']['count']:.0f} {m['random']['count']:.0f} {gate}"
                )
    print()
    print(f"EVENT_RESOLVED_TRUE_C4_SURVIVAL {survive}/{trials}")
    print(f"RANDOM_FALSE_FULLSPAN_AFTER_GAP {false_random_after_gap}/{len(windows)*len(qs)*(len(gaps)-1)}")
    print(
        "Interpretation: event-resolved true C4 sheets should survive at gap 0. "
        "Temporal gap-closing is an unsafe operation if random/finite controls "
        "gain full-span components only after coarsening."
    )


if __name__ == "__main__":
    main()
