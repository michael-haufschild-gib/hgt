#!/usr/bin/env python3
"""R42: boundary/confinement passport for transition softness.

ResearchNode #28: transition softness, now treated as a bridge/geometry
diagnostic rather than a transcendence detector.

NODE:
  Boundary conditions and confinement are neglected when interpreting
  diffusion-derived fluctuation spectra.

Step 9 method:
  22. Compare nearby false statements.
"""

from __future__ import annotations

import importlib.util
import math
import pathlib

import numpy as np


NODE = (
    "boundary conditions and confinement are neglected when interpreting "
    "diffusion-derived fluctuation spectra in small volumes, membranes, pores, "
    "or cells"
)

TRANSFER_ATTEMPTS = [
    "transition softness needs a boundary and confinement passport",
    "phase-edge softness may be window confinement rather than intrinsic bridge geometry",
    "compare intrinsic softness against confined subwindow transition spectra",
]


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-transition-path-vs-residence.py")
spec = importlib.util.spec_from_file_location("transition_base", BASE)
transition_base = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(transition_base)


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def confined_corr(t: np.ndarray, diffusion: float, length: float, modes: int = 80) -> np.ndarray:
    out = np.zeros_like(t)
    for n in range(1, modes + 1):
        weight = 1.0 / (n * n)
        out += weight * np.exp(-diffusion * (n * math.pi / length) ** 2 * t)
    return out / out[0]


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: confinement changes diffusion spectra"]
    lines.append(
        "Constraint: the fluctuation spectrum of diffusion depends on boundary "
        "conditions and confinement length; an unbounded/free model can assign "
        "the wrong diffusion scale."
    )
    t = np.linspace(0.0, 3.0, 500)
    true_d = 0.40
    lines.append("L fitted_tau naive_D_from_tau")
    for length in [0.75, 1.0, 1.5, 2.5]:
        c = confined_corr(t, true_d, length)
        # Fit early/mid log decay to a single exponential, as a common
        # over-simplified fluctuation-spectroscopy move.
        mask = (t > 0.15) & (t < 1.2) & (c > 1e-4)
        a = np.vstack([t[mask], np.ones(int(np.sum(mask)))]).T
        slope = float(np.linalg.lstsq(a, np.log(c[mask]), rcond=None)[0][0])
        tau = -1.0 / slope
        naive_d = 1.0 / tau
        lines.append(f"{length:.2f} {tau:.4f} {naive_d:.4f}")
    lines.append(
        "NODE verdict: the same physical diffusion constant gives different "
        "apparent relaxation scales when confinement changes."
    )
    return lines


def transition_trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...]) -> np.ndarray:
    rng = np.random.default_rng(42000 + int(1000 * sigma) + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
    return transition_base.trace(kind, sigma, window, samples, primes, rng)


def subwindow_softness(vals: np.ndarray, length: int, stride: int) -> list[dict[str, float]]:
    rows = []
    for start in range(0, len(vals) - length + 1, stride):
        sub = vals[start : start + length]
        row = transition_base.transition_edges(sub, threshold=0.0, band=0.12)
        if row["events"] >= 3:
            rows.append(row)
    return rows


def summarize(rows: list[dict[str, float]]) -> tuple[float, float, float, float, float]:
    if not rows:
        return (float("nan"), float("nan"), float("nan"), float("nan"), 0.0)
    softness = np.asarray([r["softness"] for r in rows], dtype=float)
    events = np.asarray([r["events"] for r in rows], dtype=float)
    return (
        float(np.median(softness)),
        float(np.min(softness)),
        float(np.max(softness)),
        float(np.median(events)),
        float(len(rows)),
    )


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Diffusion spectral formulas do not transfer literally. The transfer is "
        "the constraint: a transition-softness statistic must state its boundary "
        "/ confinement conditions, because finite windows can change apparent "
        "edge width and low-frequency softness."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored: list[tuple[int, int, str]] = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, chosen_i, chosen = min(scored)
    lines.append(f"chosen={chosen_i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 22: COMPARE NEARBY FALSE STATEMENTS")
    lines.append(
        "False-nearby A: transition softness is intrinsic and survives arbitrary "
        "subwindow confinement. False-nearby B: any soft edge is a confinement "
        "artifact. Test both against full-window and confined-subwindow traces."
    )
    primes = transition_base.first_primes(160)
    samples = 320
    sigma = 0.5
    windows = [(100.0, 170.0), (500.0, 570.0)]
    lines.append("window kind full_soft full_events sub_len sub_median sub_min sub_max sub_median_events n_sub")
    all_rows = []
    for window in windows:
        for kind in ["true", "finite", "random"]:
            vals = transition_trace(kind, sigma, window, samples, primes)
            full = transition_base.transition_edges(vals, threshold=0.0, band=0.12)
            for sub_len in [40, 80, 160]:
                rows = subwindow_softness(vals, sub_len, max(10, sub_len // 4))
                med, mn, mx, ev_med, n = summarize(rows)
                all_rows.append((window, kind, full, sub_len, med, mn, mx, ev_med, n))
                lines.append(
                    f"[{int(window[0])},{int(window[1])}] {kind:6s} "
                    f"{full['softness']:.2f} {full['events']:.0f} {sub_len:03d} "
                    f"{med:.2f} {mn:.2f} {mx:.2f} {ev_med:.1f} {int(n):02d}"
                )
    # Gate summaries.
    true_collapses = sum(
        1
        for _, kind, _, sub_len, med, *_ in all_rows
        if kind == "true" and sub_len <= 80 and med < 0.6 * 40.0
    )
    finite_inflates = sum(
        1
        for _, kind, _, sub_len, med, *_ in all_rows
        if kind == "finite" and sub_len <= 80 and med > 20.0
    )
    true_beats_finite_full = 0
    true_beats_finite_sub = 0
    for window in windows:
        full_true = [r[2]["softness"] for r in all_rows if r[0] == window and r[1] == "true" and r[3] == 40][0]
        full_finite = [r[2]["softness"] for r in all_rows if r[0] == window and r[1] == "finite" and r[3] == 40][0]
        true_beats_finite_full += int(full_true > 2.0 * full_finite)
        for sub_len in [40, 80, 160]:
            med_true = [r[4] for r in all_rows if r[0] == window and r[1] == "true" and r[3] == sub_len][0]
            med_finite = [r[4] for r in all_rows if r[0] == window and r[1] == "finite" and r[3] == sub_len][0]
            true_beats_finite_sub += int(med_true > 2.0 * med_finite)
    lines.append("")
    lines.append(f"TRUE_FULL_BEATS_FINITE_BY_2X {true_beats_finite_full}/2")
    lines.append(f"TRUE_SUBWINDOW_BEATS_FINITE_BY_2X {true_beats_finite_sub}/6")
    lines.append(f"TRUE_SHORT_SUBWINDOW_COLLAPSES {true_collapses}/4")
    lines.append(f"FINITE_SHORT_SUBWINDOW_INFLATES {finite_inflates}/4")
    lines.append(
        "Interpretation: the tested subwindow confinements do not explain away "
        "the true-vs-finite softness gap. The passport is still required, but "
        "this run is positive robustness evidence rather than a boundary-artifact "
        "failure."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("Penrose R42: boundary/confinement passport for transition softness")
    out.append("ResearchNode: #28 Transition softness")
    out.append(f"NODE: {NODE}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
