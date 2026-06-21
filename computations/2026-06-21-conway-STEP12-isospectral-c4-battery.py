#!/usr/bin/env python3
"""STEP 12 stress battery for isospectral orientability -> C4.

Stress the candidate:
  Per-lane scalar Fourier spectra do not determine the cross-sigma correlation
  operator of the phase-weld field.

The battery checks:
  - exact per-lane power preservation for isospectral surrogates;
  - true-vs-isospectral collapse across several windows;
  - true-vs-finite separation in the critical strip;
  - true/finite collapse on the Euler-convergent right side.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")

first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]
phase_defect = BASE["phase_defect"]
lane_standardize = BASE["lane_standardize"]
circular_shift_lanes = BASE["circular_shift_lanes"]
fourier_scramble_lanes = BASE["fourier_scramble_lanes"]
lane_power_rel_diff = BASE["lane_power_rel_diff"]
corr_metrics = BASE["corr_metrics"]


def build_multi_fields(sigmas, window, samples, finite_sets, rng):
    fields = {"true": np.zeros((samples, len(sigmas))), "random": np.zeros((samples, len(sigmas)))}
    for n in finite_sets:
        fields[f"finite{n}"] = np.zeros((samples, len(sigmas)))
    import math

    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            fields["true"][j, i] = phase_defect(g, zp)
            fields["random"][j, i] = phase_defect(g, rp)
            for n, primes in finite_sets.items():
                fields[f"finite{n}"][j, i] = phase_defect(g, dlog_finite(s, primes))
    return fields


def main() -> None:
    rng = np.random.default_rng(2606212047)
    finite_counts = [30, 80, 160, 320]
    finite_sets = {n: first_primes(n) for n in finite_counts}
    cases = [
        ("critical_zeros", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (14.0, 84.0), "critical"),
        ("critical_low", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 170.0), "critical"),
        ("critical_mid", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (260.0, 330.0), "critical"),
        ("critical_high", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 570.0), "critical"),
        ("right_low", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (100.0, 170.0), "right"),
        ("right_high", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (500.0, 570.0), "right"),
    ]
    print("STEP 12 isospectral C4 battery")
    print(f"samples=260 finite_counts={finite_counts}")
    print(
        "case region true_eig shifted_eig fourier_eig random_eig max_finite_eig "
        "iso_gap finite_gap power_shift power_fourier adj_true xi_true span_true finite_eigs verdict"
    )
    critical_survive = 0
    critical_total = 0
    right_collapse = 0
    right_total = 0
    for label, sigmas, window, region in cases:
        fields = build_multi_fields(sigmas, window, 260, finite_sets, rng)
        true = lane_standardize(fields["true"])
        shifted = circular_shift_lanes(true, rng)
        fourier = fourier_scramble_lanes(true, rng)
        true_m = corr_metrics(true)
        shifted_m = corr_metrics(shifted)
        fourier_m = corr_metrics(fourier)
        random_m = corr_metrics(lane_standardize(fields["random"]))
        finite_eigs = []
        for n in finite_counts:
            finite_eigs.append(corr_metrics(lane_standardize(fields[f"finite{n}"])).top_eig)
        max_finite = max(finite_eigs)
        iso_gap = true_m.top_eig - max(shifted_m.top_eig, fourier_m.top_eig)
        finite_gap = true_m.top_eig - max(max_finite, random_m.top_eig)
        p_shift = lane_power_rel_diff(true, shifted)
        p_fourier = lane_power_rel_diff(true, fourier)
        if region == "critical":
            ok = iso_gap > 3.5 and finite_gap > 1.0 and p_shift < 1e-10 and p_fourier < 1e-10
            critical_survive += int(ok)
            critical_total += 1
        else:
            ok = abs(finite_gap) < 0.15 and iso_gap > 3.5 and p_shift < 1e-10 and p_fourier < 1e-10
            right_collapse += int(ok)
            right_total += 1
        print(
            f"{label:14s} {region:8s} {true_m.top_eig:.4f} {shifted_m.top_eig:.4f} "
            f"{fourier_m.top_eig:.4f} {random_m.top_eig:.4f} {max_finite:.4f} "
            f"{iso_gap:.4f} {finite_gap:.4f} {p_shift:.2e} {p_fourier:.2e} "
            f"{true_m.adj_mean:.4f} {true_m.corr_length:.4f} {true_m.span20:d} "
            + ",".join(f"N{n}:{eig:.3f}" for n, eig in zip(finite_counts, finite_eigs))
            + f" {int(ok)}"
        )
    print()
    print(f"CRITICAL_SURVIVAL {critical_survive}/{critical_total}")
    print(f"RIGHT_FINITE_COLLAPSE_WITH_ISOSPECTRAL_BREAK {right_collapse}/{right_total}")
    print(
        "Interpretation: C4 is not audible from lane scalar spectra. The "
        "isospectral lane surrogates preserve each lane's Fourier power but "
        "collapse the cross-sigma operator. The critical-strip finite-control "
        "gap remains, while on the right side finite Euler matches true even "
        "though isospectral surrogates still destroy the joint orientation."
    )


if __name__ == "__main__":
    main()
