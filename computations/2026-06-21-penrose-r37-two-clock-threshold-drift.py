#!/usr/bin/env python3
"""R37: thermal-threshold drift -> two-clock seam threshold passport.

ResearchNode #32: Two-clock seam, now reclassified as a bridge/geometry
instrument rather than a transcendence detector.

NODE:
  Thermal lensing and temperature-dependent gain shift the effective threshold
  during laser operation.

Step 9 method:
  4. Change the viewpoint.
"""

from __future__ import annotations

import math
import runpy
from dataclasses import dataclass

import numpy as np


NODE = (
    "thermal lensing and temperature-dependent gain shift the effective "
    "threshold during operation"
)

TRANSFER_ATTEMPTS = [
    "two-clock seam threshold drifts with slow source state during phase observation",
    "source-conditioned event thresholds replace fixed pump thresholds in two-clock data",
    "thermal threshold drift becomes a bridge-axis source-state quantile passport",
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


def node_validation_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: thermal threshold drift"]
    lines.append(
        "Constraint: a laser threshold cannot be specified by pump alone when a "
        "slow thermal state shifts the effective threshold during operation."
    )

    dt = 0.05
    times = np.arange(0.0, 120.0 + dt, dt)
    pump = np.where(times <= 60.0, 0.55 + 0.018 * times, 1.63 - 0.018 * (times - 60.0))
    eps = 0.03

    def simulate(tau: float, eta: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        temp = np.zeros_like(times)
        threshold = np.zeros_like(times)
        output = np.zeros_like(times)
        threshold[0] = 1.0 + eta * temp[0]
        output[0] = max(0.0, pump[0] - threshold[0])
        for i in range(1, len(times)):
            temp[i] = temp[i - 1] + dt * (0.75 * pump[i - 1] - temp[i - 1]) / tau
            threshold[i] = 1.0 + eta * temp[i]
            output[i] = max(0.0, pump[i] - threshold[i])
        return temp, threshold, output

    for tau, eta in [(6.0, 0.0), (6.0, 0.28), (22.0, 0.28)]:
        temp, threshold, output = simulate(tau, eta)
        rising = np.where((times <= 60.0) & (output > eps))[0]
        falling = np.where((times > 60.0) & (output > eps))[0]
        rise_pump = float(pump[rising[0]]) if len(rising) else float("nan")
        fall_pump = float(pump[falling[-1]]) if len(falling) else float("nan")
        thr_spread = float(np.max(threshold) - np.min(threshold))
        hysteresis = fall_pump - rise_pump
        lines.append(
            f"tau={tau:04.1f} eta={eta:.2f} rise_pump={rise_pump:.4f} "
            f"fall_pump={fall_pump:.4f} hysteresis={hysteresis:+.4f} "
            f"threshold_spread={thr_spread:.4f} final_temp={float(temp[-1]):.4f}"
        )
    lines.append(
        "NODE verdict: the apparent crossing pump shifts once the slow thermal "
        "state is coupled; a fixed pump threshold is not an invariant."
    )
    return lines


C4 = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
gamma_part = C4["gamma_part"]
dlog_zeta = C4["dlog_zeta"]
dlog_finite = C4["dlog_finite"]
first_primes = C4["first_primes"]
phase_defect = C4["phase_defect"]


def angle_diff(a: complex, b: complex) -> float:
    da = math.atan2(a.imag, a.real) - math.atan2(b.imag, b.real)
    return abs(math.atan2(math.sin(da), math.cos(da)))


@dataclass
class DriftRow:
    label: str
    sigma: float
    window: tuple[float, float]
    q: float
    finite_shift: float
    random_shift: float
    shifted_state_shift: float
    finite_event_delta: float
    random_event_delta: float
    iqr: float
    random_iqr: float


def conditional_metrics(error: np.ndarray, slow: np.ndarray, q: float) -> tuple[float, float, float]:
    high = slow >= float(np.median(slow))
    low = ~high
    fixed = float(np.quantile(error, q))
    shift = float(np.quantile(error[high], q) - np.quantile(error[low], q))
    event_delta = float(np.mean(error[high] <= fixed) - np.mean(error[low] <= fixed))
    iqr = float(np.quantile(error, 0.75) - np.quantile(error, 0.25) + 1e-12)
    return shift, event_delta, iqr


def hgt_series(
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    tgrid = np.linspace(window[0], window[1], samples)
    finite_error = np.empty(samples, dtype=float)
    random_error = np.empty(samples, dtype=float)
    source_state = np.empty(samples, dtype=float)
    for j, t in enumerate(tgrid):
        s = complex(float(sigma), float(t))
        zp = dlog_zeta(s)
        fp = dlog_finite(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        rp = abs(fp) * complex(math.cos(theta), math.sin(theta))
        finite_error[j] = angle_diff(zp, fp)
        random_error[j] = angle_diff(zp, rp)
        source_state[j] = math.log1p(abs(zp)) + phase_defect(gamma_part(s), zp)
    return finite_error, random_error, ema(source_state, tau=9.0)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Laser rate equations transfer only as a constraint schema. Direct "
        "threshold formulas reduce to ordinary dynamical-systems modelling; "
        "the HGT transfer keeps the slow-state threshold-shift test and applies "
        "it to the bridge/geometry two-clock seam."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored: list[tuple[int, int, str]] = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, chosen_i, chosen = min(scored)
    lines.append(f"chosen={chosen_i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 4: CHANGE THE VIEWPOINT")
    lines.append(
        "Viewpoint A: fixed global finite-prime phase-error threshold. "
        "Viewpoint B: source-state-conditioned threshold, measured by the "
        "difference between high-source and low-source conditional quantiles."
    )
    lines.append(
        "case sigma q finite_shift/IQR random_shift/IQR shifted_state_shift/IQR "
        "finite_event_delta random_event_delta"
    )

    primes = first_primes(160)
    rng = np.random.default_rng(37032)
    rows: list[DriftRow] = []
    cases = [
        ("critical_low", 0.30, (100.0, 170.0)),
        ("critical_mid", 0.50, (100.0, 170.0)),
        ("critical_high", 0.70, (100.0, 170.0)),
        ("critical2_low", 0.30, (500.0, 570.0)),
        ("critical2_mid", 0.50, (500.0, 570.0)),
        ("critical2_high", 0.70, (500.0, 570.0)),
        ("right_low", 1.20, (100.0, 170.0)),
        ("right_high", 1.20, (500.0, 570.0)),
    ]
    for label, sigma, window in cases:
        finite_error, random_error, source_state = hgt_series(sigma, window, 360, primes, rng)
        shifted_state = np.roll(source_state, len(source_state) // 2)
        for q in [0.40, 0.50, 0.60]:
            finite_shift, finite_event_delta, iqr = conditional_metrics(finite_error, source_state, q)
            random_shift, random_event_delta, random_iqr = conditional_metrics(random_error, source_state, q)
            shifted_shift, _, _ = conditional_metrics(finite_error, shifted_state, q)
            rows.append(
                DriftRow(
                    label=label,
                    sigma=sigma,
                    window=window,
                    q=q,
                    finite_shift=finite_shift,
                    random_shift=random_shift,
                    shifted_state_shift=shifted_shift,
                    finite_event_delta=finite_event_delta,
                    random_event_delta=random_event_delta,
                    iqr=iqr,
                    random_iqr=random_iqr,
                )
            )
            lines.append(
                f"{label:14s} {sigma:.2f} {q:.2f} "
                f"{finite_shift / iqr:+.4f} {random_shift / random_iqr:+.4f} "
                f"{shifted_shift / iqr:+.4f} {finite_event_delta:+.4f} {random_event_delta:+.4f}"
            )

    critical = [r for r in rows if r.sigma < 1.0]
    right = [r for r in rows if r.sigma > 1.0]
    crit_neg = sum(1 for r in critical if r.finite_shift / r.iqr < -0.35)
    right_pos = sum(1 for r in right if r.finite_shift / r.iqr > 0.35)
    finite_beats_random = sum(
        1
        for r in rows
        if abs(r.finite_shift / r.iqr)
        > abs(r.random_shift / max(r.random_iqr, 1e-12))
    )
    finite_beats_shifted = sum(
        1
        for r in rows
        if abs(r.finite_shift / r.iqr)
        > abs(r.shifted_state_shift / r.iqr)
    )

    lines.append("")
    lines.append(f"CRITICAL_NEGATIVE_DRIFT_ROWS {crit_neg}/{len(critical)}")
    lines.append(f"RIGHT_POSITIVE_DRIFT_ROWS {right_pos}/{len(right)}")
    lines.append(f"FINITE_BEATS_RANDOM_ABS_DRIFT {finite_beats_random}/{len(rows)}")
    lines.append(f"FINITE_BEATS_SHIFTED_STATE_ABS_DRIFT {finite_beats_shifted}/{len(rows)}")
    lines.append(
        "Interpretation: a nonzero conditional-quantile drift means the event "
        "threshold is source-state dependent. In the reoriented frame this is "
        "a bridge/geometry observation-sequence passport, not a transcendence "
        "claim."
    )
    lines.append("\nSTEP 12 FOLLOW-UP: cutoff robustness at q=0.50")
    lines.append("window sigma nprimes finite_shift/IQR event_delta shifted_state_shift/IQR")
    for window_label, window in [("low", (100.0, 170.0)), ("high", (500.0, 570.0))]:
        for sigma in [0.30, 0.50, 0.70, 1.20]:
            for nprimes in [40, 80, 160, 240]:
                fp = first_primes(nprimes)
                local_rng = np.random.default_rng(37032 + nprimes + int(1000 * sigma) + int(window[0]))
                finite_error, _, source_state = hgt_series(sigma, window, 300, fp, local_rng)
                shifted_state = np.roll(source_state, len(source_state) // 2)
                finite_shift, event_delta, iqr = conditional_metrics(finite_error, source_state, 0.50)
                shifted_shift, _, _ = conditional_metrics(finite_error, shifted_state, 0.50)
                lines.append(
                    f"{window_label:4s} {sigma:.2f} {nprimes:03d} "
                    f"{finite_shift / iqr:+.4f} {event_delta:+.4f} {shifted_shift / iqr:+.4f}"
                )
    lines.append(
        "Follow-up verdict: if the sign/magnitude survives prime-cutoff variation "
        "but also appears on the right side, it is an observation-sequence "
        "gatekeeper for two-clock evidence, not a standalone seam-localizing "
        "detector."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("Penrose R37: thermal-threshold drift -> two-clock seam threshold passport")
    out.append("ResearchNode: #32 Two-clock seam (reclassified bridge diagnostic)")
    out.append(f"NODE: {NODE}")
    out.extend(node_validation_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
