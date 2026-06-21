#!/usr/bin/env python3
"""NODE test: transient intermediates can be misidentified when hidden/overlapped.

The random NODE is chemical, not HT:
    "Misidentification of intermediates because transient species are below
     detection limits or overlap spectroscopically."

The test builds a two-intermediate truth and asks whether spectroscopy can
distinguish it from a merged one-intermediate model under overlap, noise, and
detection clipping.
"""

import argparse
import math

import numpy as np
from scipy.optimize import nnls


def gaussian(x, center, width):
    y = np.exp(-0.5 * ((x - center) / width) ** 2)
    return y / y.max()


def pulse(t, rise, decay):
    y = (1.0 - np.exp(-rise * t)) * np.exp(-decay * t)
    return y / y.max()


def fit_timewise(y, basis):
    coeffs = []
    rss = 0.0
    for row in y:
        coef, _ = nnls(basis, row)
        pred = basis @ coef
        rss += float(np.sum((row - pred) ** 2))
        coeffs.append(coef)
    return np.array(coeffs), rss


def corr(a, b):
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def run_case(separation, hidden_scale, threshold, noise, rng):
    lam = np.linspace(-1.0, 1.0, 180)
    t = np.linspace(0.0, 10.0, 160)

    eps1 = gaussian(lam, -separation / 2.0, 0.115)
    eps2 = gaussian(lam, separation / 2.0, 0.115)
    epsp = gaussian(lam, 0.55, 0.14)
    epsm = eps1 + eps2
    epsm = epsm / epsm.max()

    c1 = 0.80 * pulse(t, 0.80, 0.22)
    c2 = hidden_scale * pulse(t, 4.8, 1.35)
    cp = 0.28 * (1.0 - np.exp(-0.35 * t))

    truth = c1[:, None] * eps1[None, :] + c2[:, None] * eps2[None, :] + cp[:, None] * epsp[None, :]
    observed = truth + rng.normal(0.0, noise, size=truth.shape)
    if threshold > 0.0:
        observed = np.where(np.abs(observed) < threshold, 0.0, observed)

    basis_true = np.column_stack([eps1, eps2, epsp])
    basis_merged = np.column_stack([epsm, epsp])
    coef_true, rss_true = fit_timewise(observed, basis_true)
    coef_merged, rss_merged = fit_timewise(observed, basis_merged)

    # Blind resolution check: after removing the known product band, can the
    # intermediate block justify rank 2 rather than one merged intermediate?
    intermediate_block = observed - cp[:, None] * epsp[None, :]
    singular_values = np.linalg.svd(intermediate_block, compute_uv=False)
    noise_floor = noise * (math.sqrt(intermediate_block.shape[0]) + math.sqrt(intermediate_block.shape[1]))
    rank2_snr = float(singular_values[1] / max(noise_floor, 1e-12))
    rank_ratio = float(singular_values[1] / max(singular_values[0], 1e-12))

    nobs = observed.size
    rms_true = math.sqrt(rss_true / nobs)
    rms_merged = math.sqrt(rss_merged / nobs)
    rms_gap = rms_merged - rms_true
    overlap = float(np.dot(eps1, eps2) / math.sqrt(np.dot(eps1, eps1) * np.dot(eps2, eps2)))

    hidden_corr = corr(coef_true[:, 1], c2)
    hidden_peak_ratio = float(np.max(coef_true[:, 1]) / max(hidden_scale, 1e-12))
    hidden_snr = float(np.max(c2[:, None] * eps2[None, :]) / max(noise + threshold, 1e-12))
    merged_plausible = rank2_snr < 3.0 or rank_ratio < 0.015
    hidden_recovered = (
        hidden_corr > 0.75
        and hidden_peak_ratio > 0.45
        and hidden_snr > 2.0
        and not merged_plausible
    )

    return {
        "sep": separation,
        "hidden": hidden_scale,
        "threshold": threshold,
        "noise": noise,
        "overlap": overlap,
        "rms_true": rms_true,
        "rms_merged": rms_merged,
        "rms_gap": rms_gap,
        "hidden_corr": hidden_corr,
        "hidden_peak_ratio": hidden_peak_ratio,
        "hidden_snr": hidden_snr,
        "rank2_snr": rank2_snr,
        "rank_ratio": rank_ratio,
        "merged_plausible": merged_plausible,
        "hidden_recovered": hidden_recovered,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--noise", type=float, default=0.003)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()

    rng = np.random.default_rng(args.seed)
    print("NODE: hidden/overlapped transient intermediate spectroscopy")
    print(f"noise={args.noise}")
    print("columns: sep hidden threshold overlap hidden_snr rank2_snr rank_ratio hidden_corr peak_ratio merged_plausible hidden_recovered")

    cases = [
        (0.34, 0.20, 0.000),
        (0.18, 0.20, 0.000),
        (0.08, 0.20, 0.000),
        (0.08, 0.06, 0.000),
        (0.08, 0.06, 0.006),
        (0.04, 0.03, 0.006),
        (0.04, 0.02, 0.010),
    ]
    for sep, hidden, thresh in cases:
        r = run_case(sep, hidden, thresh, args.noise, rng)
        print(
            f"case sep={sep:.2f} hidden={hidden:.2f} threshold={thresh:.3f} "
            f"overlap={r['overlap']:.4f} hidden_snr={r['hidden_snr']:.3f} "
            f"rank2_snr={r['rank2_snr']:.3f} rank_ratio={r['rank_ratio']:.4f} "
            f"hidden_corr={r['hidden_corr']:.3f} "
            f"peak_ratio={r['hidden_peak_ratio']:.3f} "
            f"merged={int(r['merged_plausible'])} recovered={int(r['hidden_recovered'])}"
        )

    print("\nGrid: M=merged plausible, R=hidden recovered, .=ambiguous/unrecovered")
    seps = [0.34, 0.24, 0.16, 0.10, 0.06, 0.04]
    hidden_scales = [0.22, 0.12, 0.06, 0.03, 0.015]
    thresholds = [0.000, 0.004, 0.008]
    for thresh in thresholds:
        print(f"threshold={thresh:.3f}")
        print("rows hidden=0.22,0.12,0.06,0.03,0.015; cols sep=0.34,0.24,0.16,0.10,0.06,0.04")
        for hidden in hidden_scales:
            row = []
            for sep in seps:
                r = run_case(sep, hidden, thresh, args.noise, rng)
                if r["hidden_recovered"] and not r["merged_plausible"]:
                    row.append("R")
                elif r["merged_plausible"]:
                    row.append("M")
                else:
                    row.append(".")
            print(f"hidden={hidden:.3f}: {''.join(row)}")

    print("\nInterpretation: recovery requires spectral separation, above-threshold transient amplitude, and a detectable second rank.")


if __name__ == "__main__":
    main()
