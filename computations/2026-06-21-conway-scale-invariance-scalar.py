#!/usr/bin/env python3
"""THE-MACHINE tick: morphogenetic scale invariance -> Scalar Layer.

NODE:
  Scale invariance mechanisms that preserve pattern proportions.

Consolidated target:
  Scalar Layer -- |P|, log(1+|P|), |H| are useful but misleading.

STEP 9 method:
  4. Change the viewpoint.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = "scale invariance mechanisms that preserve pattern proportions"

TRANSFER_ATTEMPTS = [
    "scalar amplitude should preserve normalized event proportions under t window scaling",
    "scale invariant scalar layer would keep high amplitude proportions across windows",
    "pattern proportion preservation tests whether scalar layer is native",
]

BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur[-1:]
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    lines = ["STEP 6 NODE TEST: proportion-preserving versus fixed-wavelength patterns"]
    lines.append(
        "A scaled prepattern keeps peaks at fixed fractions of the body axis; a fixed-wavelength "
        "mechanism preserves absolute spacing and loses proportions as domain length changes."
    )
    lines.append("length scaled_peak_fracs fixed_wavelength_peak_fracs mean_fraction_error")
    template = np.array([0.2, 0.5, 0.8])
    wavelength = 0.30
    for length in [1.0, 1.5, 2.0, 3.0]:
        scaled = template
        fixed_abs = np.arange(0.2, length, wavelength)
        fixed_frac = fixed_abs / length
        nearest = np.array([fixed_frac[np.argmin(np.abs(fixed_frac - q))] for q in template])
        err = float(np.mean(np.abs(nearest - template)))
        lines.append(
            f"{length:.1f} "
            f"{','.join(f'{x:.3f}' for x in scaled)} "
            f"{','.join(f'{x:.3f}' for x in nearest)} {err:.4f}"
        )
    lines.append(
        "NODE verdict: preserving pattern proportions is a normalized-coordinate constraint, "
        "not just persistence of peaks."
    )
    return lines


def event_signature(values: np.ndarray, bins: int = 10, q: float = 0.85) -> np.ndarray:
    threshold = float(np.quantile(values, q))
    events = values >= threshold
    parts = np.array_split(np.arange(len(values)), bins)
    sig = np.array([float(np.mean(events[idx])) for idx in parts])
    total = float(np.sum(sig))
    return sig / total if total > 0 else sig


def signatures_for_window(sigma: float, window: tuple[float, float], samples: int, primes, rng):
    ts = np.linspace(window[0], window[1], samples)
    out = {"P_true": [], "H_true": [], "H_finite": [], "H_random": []}
    for t in ts:
        s = complex(float(sigma), float(t))
        a = gamma_part(s)
        p = dlog_zeta(s)
        pf = dlog_finite(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        pr = abs(p) * complex(math.cos(theta), math.sin(theta))
        out["P_true"].append(math.log1p(abs(p)))
        out["H_true"].append(math.log1p(abs(a + p)))
        out["H_finite"].append(math.log1p(abs(a + pf)))
        out["H_random"].append(math.log1p(abs(a + pr)))
    return {key: event_signature(np.array(vals)) for key, vals in out.items()}


def corr(a: np.ndarray, b: np.ndarray) -> float:
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Morphogen scaling formulas do not apply unchanged to the Scalar Layer. The minimal "
        "transfer keeps only the normalized-coordinate constraint: event proportions should "
        "survive t-window scaling if the scalar layer carries native geometry."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 4: CHANGE THE VIEWPOINT")
    lines.append("Old viewpoint: raw scalar amplitude/event rate. New viewpoint: normalized event proportions.")

    rng = np.random.default_rng(2606214619)
    primes = first_primes(160)
    windows = [
        ("low_zero", (14.0, 84.0)),
        ("critical_low", (100.0, 170.0)),
        ("critical_half", (100.0, 135.0)),
        ("critical_double", (100.0, 240.0)),
        ("critical_high", (500.0, 570.0)),
    ]
    sigmas = [0.5, 0.7, 1.2]
    lines.append("sigma window kind event_rate_signature corr_to_low_zero corr_to_finite corr_to_random")
    base_by_sigma = {}
    all_sigs = {}
    for sigma in sigmas:
        all_sigs[sigma] = {}
        for label, window in windows:
            all_sigs[sigma][label] = signatures_for_window(sigma, window, 420, primes, rng)
        base_by_sigma[sigma] = all_sigs[sigma]["low_zero"]["H_true"]
        for label, _ in windows:
            h_true = all_sigs[sigma][label]["H_true"]
            finite = all_sigs[sigma][label]["H_finite"]
            random = all_sigs[sigma][label]["H_random"]
            lines.append(
                f"{sigma:.1f} {label:15s} H_true "
                f"{','.join(f'{x:.2f}' for x in h_true)} "
                f"{corr(h_true, base_by_sigma[sigma]):+.4f} {corr(h_true, finite):+.4f} {corr(h_true, random):+.4f}"
            )
    finite_match = []
    random_match = []
    scale_stability = []
    for sigma in sigmas:
        base = base_by_sigma[sigma]
        for label, _ in windows[1:]:
            h_true = all_sigs[sigma][label]["H_true"]
            finite = all_sigs[sigma][label]["H_finite"]
            random = all_sigs[sigma][label]["H_random"]
            scale_stability.append(corr(h_true, base))
            finite_match.append(corr(h_true, finite))
            random_match.append(corr(h_true, random))
    lines.append("")
    lines.append(f"MEAN_SCALE_STABILITY_TO_LOW_ZERO {float(np.mean(scale_stability)):+.4f}")
    lines.append(f"MEAN_TRUE_FINITE_SIGNATURE_CORR {float(np.mean(finite_match)):+.4f}")
    lines.append(f"MEAN_TRUE_RANDOM_SIGNATURE_CORR {float(np.mean(random_match)):+.4f}")
    lines.append(
        "Interpretation: if finite/random signatures match true as well as, or better than, "
        "cross-window scale stability, then normalized scalar proportions do not rescue the Scalar Layer."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: morphogenetic scale invariance -> Scalar Layer")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 26/32 Scalar Layer")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
