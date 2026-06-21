#!/usr/bin/env python3
"""R39: reporter-normalization passport for source-built index equivalence.

ResearchNode #14: index equivalence / source-built kappa_-.

NODE:
  Interpreting reporter fluorescence as quorum sensing output without
  correcting for growth rate, plasmid copy number, maturation time, or
  metabolic burden.

Step 9 method:
  17. Change representation.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np


NODE = (
    "interpreting reporter fluorescence as quorum sensing output without "
    "correcting for growth rate, plasmid copy number, maturation time, or "
    "metabolic burden"
)

TRANSFER_ATTEMPTS = [
    "source-built kappa reporters need growth copy maturation burden normalization",
    "index equivalence must distinguish faithful inertia from reporter projection",
    "change scalar reporter readout into a signed quadratic-form passport",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def ema(x: np.ndarray, tau: float) -> np.ndarray:
    alpha = 1.0 - math.exp(-1.0 / tau)
    y = np.empty_like(x, dtype=float)
    y[0] = x[0]
    for i in range(1, len(x)):
        y[i] = (1.0 - alpha) * y[i - 1] + alpha * x[i]
    return y


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: reporter fluorescence is not raw QS output"]
    lines.append(
        "Constraint: raw reporter fluorescence equals response convolved with "
        "growth, copy number, maturation, and burden; it is not the biological "
        "quorum-sensing output without corrections."
    )
    t = np.linspace(0.0, 16.0, 321)
    density_a = np.exp(0.24 * t)
    density_b = np.exp(0.36 * t)
    signal_a = 1.0 / (1.0 + np.exp(-(t - 7.5)))
    signal_b = 0.72 / (1.0 + np.exp(-(t - 5.0)))
    copy_a = 1.0 + 0.6 * np.sin(0.45 * t) ** 2
    copy_b = 3.0 - 0.5 * np.sin(0.35 * t + 0.4)
    burden_a = 1.0 / (1.0 + 0.06 * density_a / density_a[-1] * 20.0)
    burden_b = 1.0 / (1.0 + 0.10 * density_b / density_b[-1] * 20.0)
    raw_a = ema(signal_a * density_a * copy_a * burden_a, tau=14.0)
    raw_b = ema(signal_b * density_b * copy_b * burden_b, tau=14.0)
    od_norm_a = raw_a / density_a
    od_norm_b = raw_b / density_b
    full_norm_a = raw_a / (density_a * copy_a * burden_a + 1e-12)
    full_norm_b = raw_b / (density_b * copy_b * burden_b + 1e-12)

    def end_mean(x: np.ndarray) -> float:
        return float(np.mean(x[-60:]))

    lines.append("strain raw_end od_norm_end full_norm_end true_signal_end")
    lines.append(
        f"A {end_mean(raw_a):.4f} {end_mean(od_norm_a):.4f} "
        f"{end_mean(full_norm_a):.4f} {end_mean(signal_a):.4f}"
    )
    lines.append(
        f"B {end_mean(raw_b):.4f} {end_mean(od_norm_b):.4f} "
        f"{end_mean(full_norm_b):.4f} {end_mean(signal_b):.4f}"
    )
    raw_rank = "A>B" if end_mean(raw_a) > end_mean(raw_b) else "B>A"
    true_rank = "A>B" if end_mean(signal_a) > end_mean(signal_b) else "B>A"
    full_rank = "A>B" if end_mean(full_norm_a) > end_mean(full_norm_b) else "B>A"
    lines.append(f"rank raw={raw_rank} full_norm={full_rank} true={true_rank}")
    lines.append(
        "NODE verdict: raw fluorescence can invert or distort the biological "
        "response ranking; normalization provenance is part of the measurement."
    )
    return lines


def random_orthogonal(rng: np.random.Generator, n: int) -> np.ndarray:
    a = rng.normal(size=(n, n))
    q, r = np.linalg.qr(a)
    signs = np.sign(np.diag(r))
    signs[signs == 0] = 1.0
    return q * signs


def inertia(a: np.ndarray, tol: float = 1e-9) -> tuple[int, int, int, float]:
    eig = np.linalg.eigvalsh((a + a.T) / 2.0)
    return (
        int(np.sum(eig < -tol)),
        int(np.sum(np.abs(eig) <= tol)),
        int(np.sum(eig > tol)),
        float(np.min(eig)),
    )


def maturation_kernel(n: int, width: float) -> np.ndarray:
    k = np.zeros((n, n), dtype=float)
    for i in range(n):
        weights = []
        js = []
        for j in range(i + 1):
            w = math.exp(-(i - j) / width)
            weights.append(w)
            js.append(j)
        weights_arr = np.asarray(weights)
        weights_arr /= float(np.sum(weights_arr))
        for j, w in zip(js, weights_arr):
            k[i, j] = float(w)
    return k


@dataclass
class Trial:
    neg_true: int
    neg_congruence: int
    raw_reporter_negative: bool
    matured_reporter_negative: bool
    projected_inertia_neg: int
    corrected_inertia_neg: int
    min_true: float
    min_projected: float
    min_corrected: float


def one_trial(rng: np.random.Generator, n: int = 14) -> Trial:
    # A sparse/dust-like negative square: exactly the thing a faithful index must
    # detect and a scalar reporter can easily miss.
    spectrum = np.linspace(0.15, 2.2, n)
    spectrum[0] = -0.045
    q = random_orthogonal(rng, n)
    base = q @ np.diag(spectrum) @ q.T
    growth = np.exp(rng.normal(0.0, 0.35, size=n))
    copy = np.exp(rng.normal(0.0, 0.25, size=n))
    burden = np.exp(rng.normal(0.0, 0.18, size=n))
    d = np.diag(growth * copy / burden)
    raw = d @ base @ d
    # Raw reporter reads only axis powers; maturation smears those powers across
    # order/truncation. Both are projections, not faithful forms.
    reporter = np.diag(raw)
    matured_reporter = maturation_kernel(n, width=2.8) @ reporter
    # A non-congruence projection that keeps only reporter diagonal information.
    projected = np.diag(matured_reporter)
    corrected = np.linalg.inv(d) @ raw @ np.linalg.inv(d)
    true_i = inertia(base)
    congr_i = inertia(raw)
    proj_i = inertia(projected)
    corr_i = inertia(corrected)
    return Trial(
        neg_true=true_i[0],
        neg_congruence=congr_i[0],
        raw_reporter_negative=bool(np.min(reporter) < 0.0),
        matured_reporter_negative=bool(np.min(matured_reporter) < 0.0),
        projected_inertia_neg=proj_i[0],
        corrected_inertia_neg=corr_i[0],
        min_true=true_i[3],
        min_projected=proj_i[3],
        min_corrected=corr_i[3],
    )


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Reporter kinetics do not transfer as biology. The transferable "
        "constraint is representational: a measured scalar reporter is not a "
        "faithful signed index unless its normalization is a congruence or has "
        "an explicit correction back to one."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored: list[tuple[int, int, str]] = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, chosen_i, chosen = min(scored)
    lines.append(f"chosen={chosen_i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 17: CHANGE REPRESENTATION")
    lines.append(
        "Change representation from scalar reporter vector to signed quadratic "
        "form. Positive growth/copy/burden corrections are safe only as "
        "congruence; diagonal reporter projection and maturation smoothing are "
        "not faithful index operations."
    )
    rng = np.random.default_rng(39014)
    trials = [one_trial(rng) for _ in range(80)]
    neg_true = sum(t.neg_true == 1 for t in trials)
    congr_preserves = sum(t.neg_congruence == t.neg_true for t in trials)
    raw_sees = sum(t.raw_reporter_negative for t in trials)
    matured_sees = sum(t.matured_reporter_negative for t in trials)
    projected_sees = sum(t.projected_inertia_neg == t.neg_true for t in trials)
    corrected_recovers = sum(t.corrected_inertia_neg == t.neg_true for t in trials)
    lines.append("TRIALS 80")
    lines.append(f"TRUE_NEGATIVE_INDEX {neg_true}/80")
    lines.append(f"CONGRUENCE_PRESERVES_INDEX {congr_preserves}/80")
    lines.append(f"RAW_DIAGONAL_REPORTER_SEES_NEGATIVE {raw_sees}/80")
    lines.append(f"MATURED_REPORTER_SEES_NEGATIVE {matured_sees}/80")
    lines.append(f"PROJECTED_REPORTER_INERTIA_MATCHES {projected_sees}/80")
    lines.append(f"CORRECTED_CONGRUENCE_INERTIA_RECOVERS {corrected_recovers}/80")
    worst = min(trials, key=lambda t: t.min_projected)
    median_projected = float(np.median([t.min_projected for t in trials]))
    median_corrected = float(np.median([t.min_corrected for t in trials]))
    lines.append(
        f"MEDIAN_MIN_EIG projected={median_projected:+.6f} corrected={median_corrected:+.6f}"
    )
    lines.append(
        f"WORST_PROJECTED_MIN_EIG {worst.min_projected:+.6f} with true_min={worst.min_true:+.6f}"
    )
    lines.append(
        "Interpretation: the faithful negative square survives every reporter "
        "normalization that is a congruence, but scalar reporter/projection "
        "representations can report positivity in all trials."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("Penrose R39: reporter-normalization passport for index equivalence")
    out.append("ResearchNode: #14 Index equivalence / source-built kappa_-")
    out.append(f"NODE: {NODE}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
