#!/usr/bin/env python3
"""THE-MACHINE tick: finite-size rounding -> B2 two-lemma bridge.

NODE:
  Finite-size rounding can make separate transitions look like a single
  multicritical point.

Consolidated target:
  B2 -- the two-lemma bridge:
    Lemma 1 detect: off-line zero => off-seam transport defect.
    Lemma 2 confine: all source-carrying coupled-lane transport defects live
    on Re(s)=1/2.

STEP 9 method:
  10. Test extreme cases.
"""

from __future__ import annotations

import math

import numpy as np


NODE = "finite size rounding can make separate transitions look like a single multicritical point"

TRANSFER_ATTEMPTS = [
    "finite resolution can make separate off seam source defects look like one B2 seam defect",
    "B2 detect confine tests need multiscale resolution against rounded defect clusters",
    "off line transport defects can be merged by smoothing into apparent seam confinement",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def gaussian(x: np.ndarray, center: float, width: float) -> np.ndarray:
    return np.exp(-0.5 * ((x - center) / width) ** 2)


def count_peaks(y: np.ndarray, threshold_fraction: float = 0.25) -> tuple[int, list[int]]:
    threshold = float(np.max(y) * threshold_fraction)
    peaks = []
    for i in range(1, len(y) - 1):
        if y[i] >= threshold and y[i] >= y[i - 1] and y[i] >= y[i + 1]:
            if peaks and i - peaks[-1] <= 2:
                if y[i] > y[peaks[-1]]:
                    peaks[-1] = i
            else:
                peaks.append(i)
    return len(peaks), peaks


def node_rows() -> list[str]:
    lines = ["STEP 6 NODE TEST: finite-size rounding of two nearby transitions"]
    lines.append(
        "Two genuine transition peaks at +/-d are observed through a finite-size "
        "rounding width w. The constraint is that peak-count at one resolution "
        "does not decide true multicriticality."
    )
    xs = np.linspace(-1.0, 1.0, 2001)
    lines.append("d width d_over_width peak_count apparent_peak_positions verdict")
    for d in [0.02, 0.05, 0.10, 0.20, 0.40]:
        for w in [0.02, 0.05, 0.10, 0.20]:
            y = gaussian(xs, -d, w) + gaussian(xs, d, w)
            n, peaks = count_peaks(y)
            pos = [float(xs[i]) for i in peaks]
            verdict = "merged" if n == 1 else "resolved"
            lines.append(
                f"{d:.2f} {w:.2f} {d / w:.2f} {n:d} "
                f"{','.join(f'{p:.3f}' for p in pos)} {verdict}"
            )
    lines.append("NODE verdict: if d/w is small, two transitions are falsely counted as one.")
    return lines


def source_density(sigmas: np.ndarray, centers: list[float], width: float) -> np.ndarray:
    y = np.zeros_like(sigmas)
    for c in centers:
        y += gaussian(sigmas, c, width)
    return y / (np.sum(y) + 1e-300)


def apparent_source_metrics(delta: float, width: float, grid: np.ndarray) -> dict[str, float | int | str]:
    centers = [0.5 - delta, 0.5 + delta]
    y = source_density(grid, centers, width)
    n, peaks = count_peaks(y, threshold_fraction=0.10)
    mean = float(np.sum(grid * y))
    variance = float(np.sum((grid - mean) ** 2 * y))
    seam_mass = float(np.sum(y[np.abs(grid - 0.5) <= width]))
    off_mass = float(np.sum(y[np.abs(grid - 0.5) > width]))
    apparent = "false_seam_single" if n == 1 and abs(mean - 0.5) < 1e-6 else "resolved_or_offseam"
    return {
        "peak_count": n,
        "mean_sigma": mean,
        "std_sigma": math.sqrt(variance),
        "seam_band_mass": seam_mass,
        "off_band_mass": off_mass,
        "apparent": apparent,
    }


def contour_count_for_pair(delta: float, half_width: float) -> int:
    # Local source model with two simple poles at sigma=0.5 +/- delta.
    return int((0.5 - half_width <= 0.5 - delta <= 0.5 + half_width)) + int(
        (0.5 - half_width <= 0.5 + delta <= 0.5 + half_width)
    )


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Finite-size peak-rounding formulas are NODE-side diagnostics. Applied "
        "unchanged they are smoothing arithmetic, not B2 source transport. The "
        "transfer changes the observable to a smoothed source-measure profile "
        "for an off-seam symmetric source pair."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 10: TEST EXTREME CASES")
    lines.append(
        "Extreme B2 surrogate: two off-seam simple sources at 0.5 +/- delta. "
        "A smoothed one-resolution source profile can look like a single seam "
        "source; contour charge with half-width < delta detects the split."
    )
    grid = np.linspace(0.0, 1.0, 2001)
    lines.append(
        "delta smooth_width delta_over_width peak_count mean_sigma std_sigma "
        "seam_band_mass off_band_mass contour_hw_half_delta contour_hw_2delta apparent"
    )
    for delta in [0.005, 0.01, 0.02, 0.05, 0.10]:
        for width in [0.005, 0.01, 0.02, 0.05, 0.10]:
            m = apparent_source_metrics(delta, width, grid)
            c_small = contour_count_for_pair(delta, 0.5 * delta)
            c_large = contour_count_for_pair(delta, 2.0 * delta)
            lines.append(
                f"{delta:.3f} {width:.3f} {delta / width:.2f} "
                f"{int(m['peak_count']):d} {float(m['mean_sigma']):.6f} {float(m['std_sigma']):.6f} "
                f"{float(m['seam_band_mass']):.4f} {float(m['off_band_mass']):.4f} "
                f"{c_small:d} {c_large:d} {m['apparent']}"
            )
    lines.append(
        "\nB2 provisional verdict: a one-scale smoothed source observable can "
        "misclassify symmetric off-seam pairs as seam-confined. The detect "
        "half of B2 needs a scale gate: either contour charge below the "
        "off-seam separation or a multiscale split test."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: finite-size rounding -> B2 two-lemma bridge")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 16/32 B2 two-lemma bridge")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
