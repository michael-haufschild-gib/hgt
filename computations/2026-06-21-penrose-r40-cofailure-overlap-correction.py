#!/usr/bin/env python3
"""R40: inner-filter overlap correction for co-failure sheets.

ResearchNode #24: co-failure sheets, reclassified as a bridge/geometry
instrument with source-lane provenance.

NODE:
  Apparent quenching caused by simple absorbance overlap rather than true
  excited-state deactivation.

Step 9 method:
  12. Find an invariant.
"""

from __future__ import annotations

import importlib.util
import math
import pathlib

import numpy as np


NODE = (
    "apparent quenching caused by simple absorbance overlap rather than true "
    "excited-state deactivation"
)

TRANSFER_ATTEMPTS = [
    "co-failure sheets may be simple amplitude-overlap not source deactivation",
    "subtract inner-filter overlap before claiming source-lane co-failure",
    "co-failure invariant is residual angle cancellation after overlap correction",
]


BASE = pathlib.Path(__file__).with_name("2026-06-21-hgt-STEP12-frailty-lane-alignment-battery.py")
spec = importlib.util.spec_from_file_location("frailty", BASE)
frailty = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(frailty)


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: overlap quenching vs deactivation"]
    lines.append(
        "Constraint: absorbance overlap can reduce measured intensity without "
        "true excited-state deactivation. Lifetime is an invariant that should "
        "not change for pure inner-filter overlap."
    )
    quencher = np.linspace(0.0, 5.0, 51)
    true_lifetime = 4.2 / (1.0 + 0.28 * quencher)
    true_intensity = 1000.0 / (1.0 + 0.28 * quencher)
    absorbance = 0.12 * quencher
    overlap_intensity = 1000.0 * 10.0 ** (-absorbance)
    overlap_lifetime = np.full_like(quencher, 4.2)
    sv_true_i = true_intensity[0] / true_intensity[-1]
    sv_overlap_i = overlap_intensity[0] / overlap_intensity[-1]
    sv_true_tau = true_lifetime[0] / true_lifetime[-1]
    sv_overlap_tau = overlap_lifetime[0] / overlap_lifetime[-1]
    lines.append("case intensity_ratio lifetime_ratio")
    lines.append(f"dynamic_quench {sv_true_i:.4f} {sv_true_tau:.4f}")
    lines.append(f"overlap_filter {sv_overlap_i:.4f} {sv_overlap_tau:.4f}")
    lines.append(
        "NODE verdict: intensity loss alone cannot certify quenching; an "
        "overlap-invariant channel such as lifetime is needed."
    )
    return lines


def gamma_part(s: complex) -> complex:
    return frailty.gamma_part(s)


def dlog(kind: str, s: complex, primes: tuple[int, ...], rng: np.random.Generator) -> complex:
    true_p = frailty.dlog_zeta(s)
    finite_p = frailty.dlog_finite_euler(s, primes)
    if kind == "true":
        return true_p
    if kind == "finite":
        return finite_p
    if kind == "random-phase":
        theta = float(rng.uniform(-math.pi, math.pi))
        return abs(true_p) * complex(math.cos(theta), math.sin(theta))
    raise ValueError(kind)


def phase_defect_and_overlap(g: complex, p: complex) -> tuple[float, float]:
    ag = abs(g)
    ap = abs(p)
    d = frailty.phase_defect(g, p)
    overlap = min(ag, ap) / (max(ag, ap) + 1e-300)
    return d, overlap


def lane_scores(kind: str, sigmas: list[float], window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    phase = np.zeros((len(sigmas), samples), dtype=float)
    overlap = np.zeros_like(phase)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(np.linspace(window[0], window[1], samples)):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            p = dlog(kind, s, primes, rng)
            phase[i, j], overlap[i, j] = phase_defect_and_overlap(g, p)
    residual = np.zeros_like(phase)
    for i in range(len(sigmas)):
        b = overlap[i]
        a = np.vstack([b, b * b, np.ones_like(b)]).T
        pred = a @ np.linalg.lstsq(a, phase[i], rcond=None)[0]
        residual[i] = phase[i] - pred
    return phase, overlap, residual


def reserve_from_badness(score: np.ndarray) -> np.ndarray:
    reserve = np.empty_like(score)
    n = score.shape[1]
    for i in range(score.shape[0]):
        order = np.argsort(score[i])
        ranks = np.empty(n, dtype=float)
        ranks[order] = np.arange(n, dtype=float)
        # Higher badness -> lower reserve. Threshold .2 means top 20% bad events.
        reserve[i] = 1.0 - ranks / max(1.0, n - 1.0)
    return reserve


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Stern-Volmer / inner-filter correction formulas do not transfer "
        "literally. The transferable constraint is an invariant split: apparent "
        "failure caused by magnitude overlap must be subtracted before claiming "
        "source-lane co-failure."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored: list[tuple[int, int, str]] = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, chosen_i, chosen = min(scored)
    lines.append(f"chosen={chosen_i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 12: FIND AN INVARIANT")
    lines.append(
        "Invariant candidate: phase co-failure should survive after subtracting "
        "the magnitude-overlap/inner-filter component `min(|Gamma|,|P|)/max(...)`. "
        "Residual co-failure is the angle/source part."
    )
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7]
    primes = frailty.first_primes(100)
    threshold = 0.20
    rows = []
    abs_rows = []
    for label, window in [("low", (100.0, 170.0)), ("high", (500.0, 570.0))]:
        for kind, seed in [("true", 4001), ("finite", 4101), ("random-phase", 4201)]:
            abs_reserve = frailty.lane_matrix(kind, sigmas, window, 140, primes, seed=seed, mode="phase")
            abs_rows.append((label, kind, frailty.metric(abs_reserve, threshold, seed=8000 + len(abs_rows))))
            phase, overlap, residual = lane_scores(kind, sigmas, window, 140, primes, seed)
            for score_name, score in [("phase", phase), ("overlap", overlap), ("residual", residual)]:
                reserve = reserve_from_badness(score)
                m = frailty.metric(reserve, threshold, seed=9000 + len(rows))
                rows.append((label, kind, score_name, m))
    lines.append("ABSOLUTE_RESERVE_BASELINE")
    lines.append("window kind visible excess_indep excess_shift mean_lows_given")
    for label, kind, m in abs_rows:
        lines.append(
            f"{label:4s} {kind:12s} {m['visible']:.3f} "
            f"{m['excess_indep']:+.3f} {m['excess_shift']:+.3f} "
            f"{m['mean_lows_given_visible']:.3f}"
        )
    lines.append("window kind score visible excess_indep excess_shift mean_lows_given")
    for label, kind, score_name, m in rows:
        lines.append(
            f"{label:4s} {kind:12s} {score_name:8s} "
            f"{m['visible']:.3f} {m['excess_indep']:+.3f} "
            f"{m['excess_shift']:+.3f} {m['mean_lows_given_visible']:.3f}"
        )
    true_resid_positive = sum(
        1
        for label, kind, score_name, m in rows
        if kind == "true" and score_name == "residual" and m["excess_indep"] > 0.08 and m["excess_shift"] > 0.08
    )
    finite_resid_positive = sum(
        1
        for label, kind, score_name, m in rows
        if kind == "finite" and score_name == "residual" and m["excess_indep"] > 0.08 and m["excess_shift"] > 0.08
    )
    overlap_positive = sum(
        1
        for label, kind, score_name, m in rows
        if score_name == "overlap" and m["excess_indep"] > 0.08 and m["excess_shift"] > 0.08
    )
    abs_true_positive = sum(
        1 for label, kind, m in abs_rows if kind == "true" and m["excess_indep"] > 0.08 and m["excess_shift"] > 0.08
    )
    abs_finite_positive = sum(
        1 for label, kind, m in abs_rows if kind == "finite" and m["excess_indep"] > 0.08 and m["excess_shift"] > 0.08
    )
    lines.append("")
    lines.append(f"ABS_TRUE_PHASE_POSITIVE {abs_true_positive}/2")
    lines.append(f"ABS_FINITE_PHASE_POSITIVE {abs_finite_positive}/2")
    lines.append(f"TRUE_RESIDUAL_COFAILURE_POSITIVE {true_resid_positive}/2")
    lines.append(f"FINITE_RESIDUAL_COFAILURE_POSITIVE {finite_resid_positive}/2")
    lines.append(f"OVERLAP_ONLY_POSITIVE_ROWS {overlap_positive}/6")
    lines.append(
        "Interpretation: if the absolute-reserve baseline separates true from "
        "finite but rank-normalized overlap/residual rows do not, the invariant "
        "is not residualization alone; absolute source-reserve calibration is "
        "load-bearing."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("Penrose R40: inner-filter overlap correction for co-failure sheets")
    out.append("ResearchNode: #24 Co-failure sheets")
    out.append(f"NODE: {NODE}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
