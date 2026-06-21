#!/usr/bin/env python3
"""STEP 11 for stochastic resonance -> landscape layers.

Method 5: make it visual.
Build eta-by-layer ridge maps for finite+noise controls against the true
landscape layers.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-stochastic-resonance-landscape-layers.py")

first_primes = BASE["first_primes"]
build_base = BASE["build_base"]
layer_fields = BASE["layer_fields"]
perturb_finite = BASE["perturb_finite"]
corr = BASE["corr"]
lane_standardize = BASE["lane_standardize"]
corr_metrics = BASE["corr_metrics"]


def spark(values):
    chars = " .:-=+*#%@"
    arr = np.asarray(values, dtype=float)
    lo = float(np.min(arr))
    hi = float(np.max(arr))
    if hi - lo < 1e-12:
        return chars[-1] * len(arr)
    idx = np.floor((arr - lo) / (hi - lo) * (len(chars) - 1)).astype(int)
    return "".join(chars[i] for i in idx)


def main() -> None:
    rng = np.random.default_rng(2606217713)
    primes = first_primes(160)
    etas = np.linspace(0.0, 2.4, 13)
    cases = [
        ("critical_low", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 170.0)),
        ("critical_high", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 570.0)),
        ("right_low", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (100.0, 170.0)),
    ]
    print("STEP 11 stochastic-resonance landscape visual map")
    print("method=5 make it visual")
    print("eta_grid " + ",".join(f"{x:.2f}" for x in etas))
    print("case layer sparkline best_eta best_score first_score last_score")
    ridge_mismatch = 0
    for label, sigmas, window in cases:
        base = build_base(sigmas, window, 240, primes, rng)
        true_layers = layer_fields(base["A"], base["P_true"])
        true_top = corr_metrics(lane_standardize(true_layers["phaseDelta"])).top_eig
        scores = {"scalarH": [], "scalarP": [], "phaseDelta": [], "c4Ratio": []}
        for eta in etas:
            layers = layer_fields(base["A"], perturb_finite(base, float(eta), rng))
            scores["scalarH"].append(corr(layers["scalarH"], true_layers["scalarH"]))
            scores["scalarP"].append(corr(layers["scalarP"], true_layers["scalarP"]))
            scores["phaseDelta"].append(corr(layers["phaseDelta"], true_layers["phaseDelta"]))
            scores["c4Ratio"].append(corr_metrics(lane_standardize(layers["phaseDelta"])).top_eig / (true_top + 1e-300))
        bests = {}
        for layer, vals in scores.items():
            vals = np.array(vals)
            best = int(np.argmax(vals))
            bests[layer] = best
            print(
                f"{label:13s} {layer:10s} {spark(vals)} {etas[best]:.2f} "
                f"{float(vals[best]):+.4f} {float(vals[0]):+.4f} {float(vals[-1]):+.4f}"
            )
        ridge_mismatch += int(len({bests["scalarH"], bests["phaseDelta"], bests["c4Ratio"]}) > 1)
    print()
    print(f"RIDGE_MISMATCH_CASES {ridge_mismatch}/{len(cases)}")
    print(
        "Interpretation: ridge mismatch is a warning against tuning one layer. Here the maps are "
        "not strong enough for a finding because no tuned scalar ridge reaches true-like phase/C4 "
        "agreement in the critical strip."
    )


if __name__ == "__main__":
    main()
