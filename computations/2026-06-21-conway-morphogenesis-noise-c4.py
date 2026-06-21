#!/usr/bin/env python3
"""THE-MACHINE tick: morphogenesis initial-noise structure -> C4.

NODE:
  Initial noise structure affects which pattern mode is selected.

Consolidated target:
  C4 -- cross-lane correlation length xi_sigma.

STEP 9 method:
  11. Run experiments.
"""

from __future__ import annotations

import math
import runpy

import mpmath as mp
import numpy as np


NODE = "initial noise structure affects which pattern mode is selected"

TRANSFER_ATTEMPTS = [
    "initial sigma noise spectrum can select apparent C4 cross lane mode",
    "C4 xi sigma must survive correlated random phase seed controls",
    "cross lane pattern mode selection can be faked by surrogate phase spectrum",
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
    modes = np.arange(1, 41)
    growth = 0.18 * np.exp(-0.5 * ((modes - 8) / 1.7) ** 2) + 0.17 * np.exp(
        -0.5 * ((modes - 15) / 1.9) ** 2
    ) - 0.035
    spectra = {
        "low_mode_seed": np.exp(-0.5 * ((modes - 8) / 1.1) ** 2),
        "high_mode_seed": np.exp(-0.5 * ((modes - 15) / 1.1) ** 2),
        "notch_both": 1.0 - np.maximum(
            np.exp(-0.5 * ((modes - 8) / 2.0) ** 2),
            np.exp(-0.5 * ((modes - 15) / 2.0) ** 2),
        ),
        "flat_white": np.ones_like(modes, dtype=float),
    }
    lines = ["STEP 6 NODE TEST: initial noise selects the visible pattern mode"]
    lines.append(
        "Two unstable mode bands are present. The final mode is selected by the seed spectrum's "
        "projection before nonlinear saturation would occur."
    )
    lines.append("seed overlap_low overlap_high final_amp dominant_mode")
    for name, amp0 in spectra.items():
        final = amp0 * np.exp(growth * 25.0)
        low_overlap = float(np.linalg.norm(amp0[(modes >= 6) & (modes <= 10)]) / np.linalg.norm(amp0))
        high_overlap = float(np.linalg.norm(amp0[(modes >= 13) & (modes <= 17)]) / np.linalg.norm(amp0))
        dom = int(modes[int(np.argmax(final))])
        lines.append(f"{name:14s} {low_overlap:.4f} {high_overlap:.4f} {float(np.linalg.norm(final)):.6e} {dom:02d}")
    lines.append(
        "NODE verdict: the same growth operator can yield low-mode, high-mode, or no clean pattern "
        "depending on the initial spectrum."
    )
    return lines


def phase_from_seed(kind: str, j: int, sigma_index: int, n_sigmas: int, rng: np.random.Generator) -> float:
    x = sigma_index / max(n_sigmas - 1, 1)
    if kind == "iid_random":
        return float(rng.uniform(-math.pi, math.pi))
    if kind == "common_mode":
        if not hasattr(phase_from_seed, "_common"):
            phase_from_seed._common = {}  # type: ignore[attr-defined]
        key = ("common", j)
        cache = phase_from_seed._common  # type: ignore[attr-defined]
        if key not in cache:
            cache[key] = float(rng.uniform(-math.pi, math.pi))
        return cache[key]
    if kind == "low_sigma_seed":
        if not hasattr(phase_from_seed, "_low"):
            phase_from_seed._low = {}  # type: ignore[attr-defined]
        cache = phase_from_seed._low  # type: ignore[attr-defined]
        if j not in cache:
            cache[j] = tuple(float(v) for v in rng.normal(scale=[1.6, 0.9, 0.45]))
        c0, c1, c2 = cache[j]
        return c0 + c1 * math.cos(math.pi * x) + c2 * math.cos(2.0 * math.pi * x)
    if kind == "high_sigma_seed":
        return float(rng.uniform(-math.pi, math.pi) + 1.2 * math.sin(8.0 * math.pi * x + 0.17 * j))
    raise ValueError(kind)


def reset_phase_seed_caches() -> None:
    for attr in ["_common", "_low"]:
        if hasattr(phase_from_seed, attr):
            delattr(phase_from_seed, attr)


def build_fields(sigmas, window, samples, primes, rng):
    kinds = ["true", "finite", "iid_random", "common_mode", "low_sigma_seed", "high_sigma_seed"]
    fields = {kind: np.zeros((samples, len(sigmas)), dtype=float) for kind in kinds}
    reset_phase_seed_caches()
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            a = gamma_part(s)
            zp = dlog_zeta(s)
            fields["true"][j, i] = phase_defect(a, zp)
            fields["finite"][j, i] = phase_defect(a, dlog_finite(s, primes))
            for kind in ["iid_random", "common_mode", "low_sigma_seed", "high_sigma_seed"]:
                theta = phase_from_seed(kind, j, i, len(sigmas), rng)
                surrogate = abs(zp) * complex(math.cos(theta), math.sin(theta))
                fields[kind][j, i] = phase_defect(a, surrogate)
    return fields


def eig_stability(field: np.ndarray) -> float:
    x = lane_standardize(field)
    full_corr = x.T @ x / x.shape[0]
    np.fill_diagonal(full_corr, 0.0)
    _, full_vecs = np.linalg.eigh(full_corr)
    full = full_vecs[:, -1]
    vals = []
    for block in np.array_split(np.arange(x.shape[0]), 4):
        xb = lane_standardize(field[block])
        corr = xb.T @ xb / xb.shape[0]
        np.fill_diagonal(corr, 0.0)
        _, vecs = np.linalg.eigh(corr)
        vals.append(abs(float(np.dot(full, vecs[:, -1]))))
    return float(np.mean(vals))


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Turing mode-selection formulas do not apply unchanged to C4. The transfer keeps the "
        "constraint: a cross-lane pattern statistic must survive controls whose initial phase "
        "seed spectrum is deliberately low-rank or common-mode."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 11: RUN EXPERIMENTS")

    rng = np.random.default_rng(2606214239)
    primes = first_primes(160)
    cases = [
        ("critical_low", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 170.0), "critical"),
        ("critical_high", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 570.0), "critical"),
        ("right_low", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (100.0, 170.0), "right"),
    ]
    lines.append("case region kind top_eig adj xi span20 eig_stability verdict")
    fake_count = 0
    total_fake_tests = 0
    for label, sigmas, window, region in cases:
        fields = build_fields(sigmas, window, 240, primes, rng)
        true_top = corr_metrics(lane_standardize(fields["true"])).top_eig
        finite_top = corr_metrics(lane_standardize(fields["finite"])).top_eig
        for kind, field in fields.items():
            m = corr_metrics(lane_standardize(field))
            stability = eig_stability(field)
            if kind in {"common_mode", "low_sigma_seed"}:
                fake = m.top_eig >= 0.85 * true_top and m.top_eig > finite_top
                fake_count += int(fake)
                total_fake_tests += 1
            else:
                fake = False
            lines.append(
                f"{label:13s} {region:8s} {kind:14s} {m.top_eig:.4f} {m.adj_mean:.4f} "
                f"{m.corr_length:.4f} {m.span20:d} {stability:.4f} {int(fake)}"
            )
    lines.append("")
    lines.append(f"CORRELATED_SEED_FAKES_C4_TOP_EIG {fake_count}/{total_fake_tests}")
    lines.append(
        "Interpretation: if common/low-sigma random phase seeds reach true-scale top eigenvalue, "
        "then C4 top-eigenvalue or xi_sigma alone is seed-spectrum vulnerable. A C4 gate must "
        "include seed-spectrum controls, per-lane spectrum preservation, or another invariant "
        "not generated by correlated random phase."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: morphogenesis initial-noise structure -> C4")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 12/32 C4 cross-lane correlation")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
