#!/usr/bin/env python3
"""R38: external catalyst accumulation audit for reset occupation.

ResearchNode #31: reset occupation, now a bridge/geometry diagnostic.

NODE:
  Misidentifying exponential growth as autocatalysis without ruling out
  external catalyst accumulation.

Step 9 method:
  16. Use a minimal counterexample.
"""

from __future__ import annotations

import math
import runpy
from dataclasses import dataclass

import numpy as np


NODE = (
    "misidentifying exponential growth as autocatalysis without ruling out "
    "external catalyst accumulation"
)

TRANSFER_ATTEMPTS = [
    "reset occupation excess may be external source accumulation not lane self-reset",
    "critical reset occupation needs a shared divisor-feed counterexample audit",
    "autocatalysis control becomes external-feed subtraction for reset occupation",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def simulate_growth(external: bool, seed: float, disable_external_at: float | None = None) -> tuple[np.ndarray, np.ndarray]:
    dt = 0.02
    t = np.arange(0.0, 18.0 + dt, dt)
    x = np.empty_like(t)
    x[0] = seed
    ext = 0.0
    for i in range(1, len(t)):
        if external:
            if disable_external_at is None or t[i - 1] < disable_external_at:
                ext += dt * 0.12
            growth = 1.4 * ext - 0.65
        else:
            growth = 10.0 * x[i - 1] - 0.65
        x[i] = max(1e-12, x[i - 1] + dt * growth * x[i - 1])
        if x[i] > 8.0:
            x[i:] = x[i]
            break
    return t, x


def log_slope(t: np.ndarray, x: np.ndarray, lo: float, hi: float) -> float:
    mask = (t >= lo) & (t <= hi) & (x > 1e-10)
    if int(np.sum(mask)) < 3:
        return float("nan")
    a = np.vstack([t[mask], np.ones(int(np.sum(mask)))]).T
    return float(np.linalg.lstsq(a, np.log(x[mask]), rcond=None)[0][0])


def growth_segment_slope(t: np.ndarray, x: np.ndarray) -> float:
    mask = (x >= 0.10) & (x <= 2.0)
    if int(np.sum(mask)) < 3:
        return float("nan")
    a = np.vstack([t[mask], np.ones(int(np.sum(mask)))]).T
    return float(np.linalg.lstsq(a, np.log(x[mask]), rcond=None)[0][0])


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: exponential growth vs external catalyst accumulation"]
    lines.append(
        "Constraint: a log-linear growth segment is insufficient evidence for "
        "autocatalysis unless an external catalyst/feed alternative is ruled out."
    )
    rows = []
    for label, external, disable in [
        ("autocatalytic_seeded", False, None),
        ("external_feed", True, None),
        ("external_feed_disabled", True, 3.0),
    ]:
        t, x = simulate_growth(external, seed=0.08, disable_external_at=disable)
        rows.append((label, growth_segment_slope(t, x), log_slope(t, x, 8.0, 12.0), float(x[-1])))
    for label, segment_slope, late_slope, final in rows:
        lines.append(
            f"{label:23s} growth_segment_slope={segment_slope:+.4f} "
            f"late_slope_8_12={late_slope:+.4f} final_x={final:.4f}"
        )
    for seed in [0.005, 0.02, 0.08, 0.20]:
        t_auto, x_auto = simulate_growth(False, seed)
        t_ext, x_ext = simulate_growth(True, seed)
        lines.append(
            f"seed={seed:.3f} auto_final={float(x_auto[-1]):.4f} "
            f"external_final={float(x_ext[-1]):.4f}"
        )
    lines.append(
        "NODE verdict: exponential-looking growth is ambiguous; seed and "
        "external-feed-removal controls distinguish true self-amplification "
        "from accumulated catalyst/feed."
    )
    return lines


C4 = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
dlog_zeta = C4["dlog_zeta"]
dlog_finite = C4["dlog_finite"]
first_primes = C4["first_primes"]


@dataclass
class AuditRow:
    label: str
    q: float
    true_excess: float
    external_excess: float
    rich_external_excess: float
    residual_excess: float
    rich_residual_excess: float
    finite_excess: float
    external_r2_center: float
    rich_external_r2_center: float
    events: int


def zscore(x: np.ndarray) -> np.ndarray:
    return (x - float(np.mean(x))) / (float(np.std(x)) + 1e-12)


def reset_events(x: np.ndarray, q: float) -> np.ndarray:
    threshold = float(np.quantile(x, q))
    hits = np.flatnonzero((x[1:] >= threshold) & (x[:-1] < threshold)) + 1
    return hits[(hits > 2) & (hits < len(x) - 3)]


def occupation_slope(x: np.ndarray, events: np.ndarray) -> float:
    xs = zscore(x)
    ages: list[float] = []
    vals: list[float] = []
    if len(events) < 2:
        return float("nan")
    for a, b in zip(events[:-1], events[1:]):
        if b <= a + 2:
            continue
        span = float(b - a)
        for k in range(a, b):
            ages.append((k - a) / span)
            vals.append(float(xs[k]))
    if len(ages) < 8:
        return float("nan")
    aa = np.asarray(ages)
    vv = np.asarray(vals)
    aa = aa - float(np.mean(aa))
    vv = vv - float(np.mean(vv))
    return float(np.dot(aa, vv) / (np.dot(aa, aa) + 1e-12))


def center_excess(slopes: tuple[float, float, float]) -> float:
    return float(slopes[1] - 0.5 * (slopes[0] + slopes[2]))


def affine_fit(common: np.ndarray, target: np.ndarray) -> tuple[np.ndarray, float]:
    a = np.vstack([common, np.ones_like(common)]).T
    beta = np.linalg.lstsq(a, target, rcond=None)[0]
    pred = a @ beta
    resid = target - pred
    ss_tot = float(np.sum((target - float(np.mean(target))) ** 2)) + 1e-12
    r2 = 1.0 - float(np.sum(resid**2)) / ss_tot
    return pred, r2


def lagged(x: np.ndarray, lag: int) -> np.ndarray:
    if lag == 0:
        return x.copy()
    out = np.empty_like(x)
    if lag > 0:
        out[:lag] = x[0]
        out[lag:] = x[:-lag]
    else:
        out[lag:] = x[-1]
        out[:lag] = x[-lag:]
    return out


def rich_feed_fit(common: np.ndarray, target: np.ndarray) -> tuple[np.ndarray, float, int]:
    best_pred = None
    best_r2 = -1e9
    best_lag = 0
    ss_tot = float(np.sum((target - float(np.mean(target))) ** 2)) + 1e-12
    for lag in range(-12, 13):
        c = lagged(common, lag)
        dc = np.gradient(c)
        a = np.vstack([c, c * c, dc, np.ones_like(c)]).T
        beta = np.linalg.lstsq(a, target, rcond=None)[0]
        pred = a @ beta
        r2 = 1.0 - float(np.sum((target - pred) ** 2)) / ss_tot
        if r2 > best_r2:
            best_pred = pred
            best_r2 = r2
            best_lag = lag
    assert best_pred is not None
    return best_pred, best_r2, best_lag


def traces(window: tuple[float, float], samples: int, nprimes: int) -> tuple[np.ndarray, np.ndarray]:
    sigmas = [0.30, 0.50, 0.70]
    primes = first_primes(nprimes)
    tgrid = np.linspace(window[0], window[1], samples)
    true = np.zeros((len(sigmas), samples), dtype=float)
    finite = np.zeros((len(sigmas), samples), dtype=float)
    for j, t in enumerate(tgrid):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            true[i, j] = math.log1p(abs(dlog_zeta(s)))
            finite[i, j] = math.log1p(abs(dlog_finite(s, primes)))
    return true, finite


def audit_case(label: str, window: tuple[float, float], q: float) -> AuditRow:
    true, finite = traces(window, samples=520, nprimes=120)
    events = reset_events(true[1], q)
    common = 0.5 * (true[0] + true[2])
    pred_center, r2_center = affine_fit(common, true[1])
    pred_left, _ = affine_fit(common, true[0])
    pred_right, _ = affine_fit(common, true[2])
    external = np.vstack([pred_left, pred_center, pred_right])
    rich_pred_center, rich_r2_center, _ = rich_feed_fit(common, true[1])
    rich_pred_left, _, _ = rich_feed_fit(common, true[0])
    rich_pred_right, _, _ = rich_feed_fit(common, true[2])
    rich_external = np.vstack([rich_pred_left, rich_pred_center, rich_pred_right])
    residual = true - external
    rich_residual = true - rich_external
    true_slopes = tuple(occupation_slope(true[i], events) for i in range(3))
    ext_slopes = tuple(occupation_slope(external[i], events) for i in range(3))
    rich_ext_slopes = tuple(occupation_slope(rich_external[i], events) for i in range(3))
    resid_slopes = tuple(occupation_slope(residual[i], events) for i in range(3))
    rich_resid_slopes = tuple(occupation_slope(rich_residual[i], events) for i in range(3))
    finite_slopes = tuple(occupation_slope(finite[i], events) for i in range(3))
    return AuditRow(
        label=label,
        q=q,
        true_excess=center_excess(true_slopes),
        external_excess=center_excess(ext_slopes),
        rich_external_excess=center_excess(rich_ext_slopes),
        residual_excess=center_excess(resid_slopes),
        rich_residual_excess=center_excess(rich_resid_slopes),
        finite_excess=center_excess(finite_slopes),
        external_r2_center=r2_center,
        rich_external_r2_center=rich_r2_center,
        events=int(len(events)),
    )


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Autocatalytic growth formulas do not transfer as equations. The only "
        "non-reducing transfer is the control logic: test whether a claimed "
        "reset-occupation excess survives an external-feed explanation."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored: list[tuple[int, int, str]] = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, chosen_i, chosen = min(scored)
    lines.append(f"chosen={chosen_i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 16: MINIMAL COUNTEREXAMPLE")
    lines.append(
        "Counterexample target: fit the center lane from an external common "
        "source proxy `0.5*(X_.3+X_.7)`. If this external-feed model reproduces "
        "the reset-occupation center excess, R15 reduces to source accumulation."
    )
    lines.append(
        "case q events true_excess affine_external rich_external "
        "affine_residual rich_residual finite_excess affine_R2 rich_R2"
    )
    rows = []
    for label, window in [("low", (100.0, 170.0)), ("high", (500.0, 570.0))]:
        for q in [0.80, 0.85, 0.90]:
            row = audit_case(label, window, q)
            rows.append(row)
            lines.append(
                f"{label:4s} {q:.2f} {row.events:03d} "
                f"{row.true_excess:+.4f} {row.external_excess:+.4f} "
                f"{row.rich_external_excess:+.4f} {row.residual_excess:+.4f} "
                f"{row.rich_residual_excess:+.4f} {row.finite_excess:+.4f} "
                f"{row.external_r2_center:.4f} {row.rich_external_r2_center:.4f}"
            )
    external_captures = sum(1 for r in rows if abs(r.external_excess) >= 0.65 * abs(r.true_excess))
    rich_external_captures = sum(1 for r in rows if abs(r.rich_external_excess) >= 0.65 * abs(r.true_excess))
    residual_keeps = sum(1 for r in rows if abs(r.residual_excess) >= 0.65 * abs(r.true_excess))
    rich_residual_keeps = sum(1 for r in rows if abs(r.rich_residual_excess) >= 0.65 * abs(r.true_excess))
    finite_matches = sum(1 for r in rows if abs(r.finite_excess) >= 0.65 * abs(r.true_excess))
    lines.append("")
    lines.append(f"EXTERNAL_CAPTURES_TRUE_EXCESS {external_captures}/{len(rows)}")
    lines.append(f"RICH_EXTERNAL_CAPTURES_TRUE_EXCESS {rich_external_captures}/{len(rows)}")
    lines.append(f"RESIDUAL_KEEPS_TRUE_EXCESS {residual_keeps}/{len(rows)}")
    lines.append(f"RICH_RESIDUAL_KEEPS_TRUE_EXCESS {rich_residual_keeps}/{len(rows)}")
    lines.append(f"FINITE_MATCHES_TRUE_EXCESS {finite_matches}/{len(rows)}")
    lines.append(
        "Interpretation: the shared external-feed model is a required "
        "counterexample audit. If it fails while the residual keeps the excess, "
        "reset occupation is not explained by common source accumulation alone."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("Penrose R38: external catalyst accumulation audit for reset occupation")
    out.append("ResearchNode: #31 Reset occupation (reclassified bridge diagnostic)")
    out.append(f"NODE: {NODE}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
