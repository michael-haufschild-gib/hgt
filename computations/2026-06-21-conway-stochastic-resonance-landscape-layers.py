#!/usr/bin/env python3
"""THE-MACHINE tick: stochastic-resonance rate matching -> landscape layers.

NODE:
  In bistable systems, stochastic resonance often depends on matching the
  noise-driven hopping rate to roughly half the period of the weak periodic
  forcing.

Consolidated target:
  Layers Of The Landscape.

STEP 9 method:
  22. Compare nearby false statements.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = (
    "in bistable systems stochastic resonance often depends on matching the noise driven "
    "hopping rate to roughly half the period of the weak periodic forcing"
)

TRANSFER_ATTEMPTS = [
    "landscape layer evidence can be falsely optimized by tuning perturbation hopping scale",
    "noise matched controls can imitate one landscape layer while failing the others",
    "layers of the landscape need a noise sweep not one tuned perturbation level",
]

BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]
phase_defect = BASE["phase_defect"]
lane_standardize = BASE["lane_standardize"]
corr_metrics = BASE["corr_metrics"]
lane_power_rel_diff = BASE["lane_power_rel_diff"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def corr(a: np.ndarray, b: np.ndarray) -> float:
    x = np.ravel(a)
    y = np.ravel(b)
    if float(np.std(x)) < 1e-12 or float(np.std(y)) < 1e-12:
        return 0.0
    return float(np.corrcoef(x, y)[0, 1])


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606217421)
    period = 80
    steps = 60 * period
    phase = np.sin(2.0 * math.pi * np.arange(steps) / period)
    rates = np.array([0.003, 0.006, 0.0125, 0.025, 0.05, 0.10, 0.20, 0.40, 0.80])
    lines = ["STEP 6 NODE TEST: stochastic resonance requires rate-period matching"]
    lines.append(
        "A two-state process has weak periodic forcing. The response is best when the mean "
        "noise-driven residence time is close to half the forcing period."
    )
    lines.append("rate mean_residence half_period_ratio response_corr transition_count")
    for rate in rates:
        state = -1.0
        out = np.zeros(steps)
        transitions = 0
        for t in range(steps):
            bias = 0.55 * phase[t] * state
            p = min(0.95, rate * math.exp(-bias))
            if rng.random() < p:
                state *= -1.0
                transitions += 1
            out[t] = state
        mean_residence = steps / max(transitions, 1)
        ratio = mean_residence / (period / 2.0)
        response = corr(out, phase)
        lines.append(f"{rate:.4f} {mean_residence:.3f} {ratio:.3f} {response:+.4f} {transitions:04d}")
    lines.append(
        "NODE verdict: the response is nonmonotone in hopping rate; a tuned rate can look "
        "special even when too little or too much noise fails."
    )
    return lines


def build_base(sigmas, window, samples, primes, rng):
    fields = {
        "A": np.zeros((samples, len(sigmas)), dtype=complex),
        "P_true": np.zeros((samples, len(sigmas)), dtype=complex),
        "P_finite": np.zeros((samples, len(sigmas)), dtype=complex),
        "P_random": np.zeros((samples, len(sigmas)), dtype=complex),
    }
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            a = gamma_part(s)
            p = dlog_zeta(s)
            pf = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            pr = abs(p) * complex(math.cos(theta), math.sin(theta))
            fields["A"][j, i] = a
            fields["P_true"][j, i] = p
            fields["P_finite"][j, i] = pf
            fields["P_random"][j, i] = pr
    return fields


def layer_fields(a: np.ndarray, p: np.ndarray) -> dict[str, np.ndarray]:
    scalar_h = np.log1p(np.abs(a + p))
    scalar_p = np.log1p(np.abs(p))
    delta = np.zeros(a.shape, dtype=float)
    for idx, _ in np.ndenumerate(a):
        delta[idx] = phase_defect(a[idx], p[idx])
    return {"scalarH": scalar_h, "scalarP": scalar_p, "phaseDelta": delta}


def perturb_finite(base, eta: float, rng: np.random.Generator) -> np.ndarray:
    p_true = base["P_true"]
    p_fin = base["P_finite"]
    theta = rng.uniform(-math.pi, math.pi, size=p_true.shape)
    noise = np.abs(p_true - p_fin) * (np.cos(theta) + 1j * np.sin(theta))
    return p_fin + eta * noise


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Kramers-rate formulas do not apply unchanged to the landscape. The transfer keeps the "
        "constraint: one tuned perturbation level can create a false optimum, so layer claims need "
        "a sweep across perturbation levels and across scalar/phase/cross-lane layers."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 22: COMPARE NEARBY FALSE STATEMENTS")
    false_statements = [
        "F1: more perturbation always worsens a layer match",
        "F2: an intermediate optimum in one layer proves landscape structure",
        "F3: a tuned perturbation that matches scalarH must also match phaseDelta and C4",
    ]
    for item in false_statements:
        lines.append(item)

    rng = np.random.default_rng(2606217517)
    primes = first_primes(160)
    cases = [
        ("critical_low", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 170.0)),
        ("critical_high", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 570.0)),
        ("right_low", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (100.0, 170.0)),
    ]
    etas = [0.0, 0.10, 0.20, 0.35, 0.55, 0.85, 1.20, 1.70]
    lines.append(
        "case eta scalarH_corr scalarP_corr phaseDelta_corr c4_top_ratio lane_power_diff "
        "scalar_only_false_match"
    )
    scalar_only_false = 0
    total_rows = 0
    for label, sigmas, window in cases:
        base = build_base(sigmas, window, 240, primes, rng)
        true_layers = layer_fields(base["A"], base["P_true"])
        true_top = corr_metrics(lane_standardize(true_layers["phaseDelta"])).top_eig
        for eta in etas:
            p = perturb_finite(base, eta, rng)
            layers = layer_fields(base["A"], p)
            scalar_h_corr = corr(layers["scalarH"], true_layers["scalarH"])
            scalar_p_corr = corr(layers["scalarP"], true_layers["scalarP"])
            phase_corr = corr(layers["phaseDelta"], true_layers["phaseDelta"])
            c4_ratio = corr_metrics(lane_standardize(layers["phaseDelta"])).top_eig / (true_top + 1e-300)
            power_diff = lane_power_rel_diff(lane_standardize(true_layers["phaseDelta"]), lane_standardize(layers["phaseDelta"]))
            false_match = scalar_h_corr > 0.90 and phase_corr < 0.60 and power_diff > 0.20
            scalar_only_false += int(false_match)
            total_rows += 1
            lines.append(
                f"{label:13s} {eta:.2f} {scalar_h_corr:+.4f} {scalar_p_corr:+.4f} "
                f"{phase_corr:+.4f} {c4_ratio:.4f} {power_diff:.4f} {int(false_match)}"
            )
    lines.append("")
    lines.append(f"SCALAR_ONLY_FALSE_MATCHES {scalar_only_false}/{total_rows}")
    lines.append(
        "Provisional interpretation: if scalarH has an intermediate high-correlation optimum while "
        "phaseDelta/C4 fail, stochastic-resonance tuning is a layer-confound, not landscape evidence."
    )
    return lines


def main() -> None:
    out = []
    out.append("THE-MACHINE tick: stochastic-resonance rate matching -> Layers Of The Landscape")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 25/32 Layers Of The Landscape")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
