#!/usr/bin/env python3
"""THE-MACHINE tick: catalyst gradient artifact -> landscape layers.

NODE:
  Mass-transport or heat gradients mistaken for intrinsic site heterogeneity.

Consolidated target:
  Layers of the landscape.

STEP 9 method:
  13. Find a monotone quantity.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = "mass transport or heat gradients mistaken for intrinsic site heterogeneity"

TRANSFER_ATTEMPTS = [
    "landscape layer differences must survive removal of smooth transport gradients",
    "phase weld and scalar layers should be separated from background gradient artifacts",
    "apparent landscape heterogeneity can be a smooth sigma t transport gradient",
]

BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]
phase_defect = BASE["phase_defect"]
lane_standardize = BASE["lane_standardize"]
corr_metrics = BASE["corr_metrics"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606215919)
    x = np.linspace(0, 1, 80)
    site_activity = rng.lognormal(mean=0.0, sigma=0.06, size=len(x))
    transport = np.exp(-2.2 * x)
    heat = 1.0 + 0.45 * x
    observed = site_activity * transport * heat
    naive_cv = float(np.std(observed) / np.mean(observed))
    corrected = observed / (transport * heat)
    corrected_cv = float(np.std(corrected) / np.mean(corrected))
    corr_gradient = float(np.corrcoef(observed, transport * heat)[0, 1])
    lines = ["STEP 6 NODE TEST: gradient artifact versus intrinsic site heterogeneity"]
    lines.append("case apparent_cv corrected_cv corr_with_transport_gradient")
    lines.append(f"identical_sites_with_gradient {naive_cv:.4f} {corrected_cv:.4f} {corr_gradient:+.4f}")
    lines.append(
        "NODE verdict: apparent heterogeneity can be dominated by transport/heat gradients; "
        "gradient correction collapses the site CV."
    )
    return lines


def polynomial_detrend(field: np.ndarray, sigmas: np.ndarray, ts: np.ndarray) -> tuple[np.ndarray, float]:
    s_grid, t_grid = np.meshgrid(sigmas, ts, indexing="ij")
    s = s_grid.ravel()
    t = (t_grid.ravel() - float(np.mean(ts))) / (float(np.std(ts)) + 1e-12)
    y = field.ravel()
    x = np.column_stack([np.ones_like(s), s, t, s * s, t * t, s * t])
    beta = np.linalg.lstsq(x, y, rcond=None)[0]
    fit = (x @ beta).reshape(field.shape)
    resid = field - fit
    frac = float(np.var(resid) / (np.var(field) + 1e-300))
    return resid, frac


def build_layer_fields(sigmas, window, samples, primes, rng):
    ts = np.linspace(window[0], window[1], samples)
    fields = {
        key: {layer: np.zeros((len(sigmas), samples), dtype=float) for layer in ["scalarH", "scalarP", "phaseDelta"]}
        for key in ["true", "finite", "random"]
    }
    for j, t in enumerate(ts):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            a = gamma_part(s)
            p = dlog_zeta(s)
            pf = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            pr = abs(p) * complex(math.cos(theta), math.sin(theta))
            for key, pp in [("true", p), ("finite", pf), ("random", pr)]:
                fields[key]["scalarH"][i, j] = math.log1p(abs(a + pp))
                fields[key]["scalarP"][i, j] = math.log1p(abs(pp))
                fields[key]["phaseDelta"][i, j] = phase_defect(a, pp)
    return ts, fields


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Catalyst gradient-correction formulas do not apply unchanged. The transfer keeps the "
        "constraint: apparent landscape-layer heterogeneity must survive smooth-gradient removal."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 13: FIND A MONOTONE QUANTITY")
    lines.append("Monotone audit quantity: residual variance fraction after removing a smooth polynomial sigma-t gradient.")
    rng = np.random.default_rng(2606216001)
    primes = first_primes(160)
    sigmas = np.linspace(0.20, 0.90, 9)
    cases = [("zero_low", (14.0, 84.0)), ("critical_low", (100.0, 170.0)), ("right_low", (100.0, 170.0))]
    lines.append("case region kind layer residual_fraction top_eig_before top_eig_after true_gap_after")
    for label, window in cases:
        region = "right" if label == "right_low" else "critical"
        use_sigmas = np.linspace(1.05, 1.70, 9) if region == "right" else sigmas
        ts, fields = build_layer_fields(use_sigmas, window, 300, primes, rng)
        residuals = {}
        for kind in ["true", "finite", "random"]:
            residuals[kind] = {}
            for layer in ["scalarH", "scalarP", "phaseDelta"]:
                resid, frac = polynomial_detrend(fields[kind][layer], use_sigmas, ts)
                residuals[kind][layer] = resid
                before = corr_metrics(lane_standardize(fields[kind][layer].T)).top_eig
                after = corr_metrics(lane_standardize(resid.T)).top_eig
                true_after = corr_metrics(lane_standardize(residuals["true"][layer].T)).top_eig if "true" in residuals and layer in residuals["true"] else after
                gap_after = true_after - after if kind != "true" else 0.0
                lines.append(
                    f"{label:12s} {region:8s} {kind:6s} {layer:10s} {frac:.4f} "
                    f"{before:.4f} {after:.4f} {gap_after:+.4f}"
                )
    lines.append(
        "\nProvisional interpretation: if a layer's residual fraction is low, it is mostly smooth-gradient "
        "background. If residual C4/top-eigen gaps survive for true against finite/random, that layer has "
        "non-smooth structure not explained by transport-gradient artifact."
    )
    return lines


def main() -> None:
    out = []
    out.append("THE-MACHINE tick: catalyst gradient artifact -> landscape layers")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 5/32 Layers of the landscape")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
