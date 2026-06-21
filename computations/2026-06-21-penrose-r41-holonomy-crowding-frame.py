#!/usr/bin/env python3
"""R41: time-varying observation-frame gate for period-domain holonomy.

ResearchNode #42: old period-domain route, now routed to Master-1
cohomology/holonomy modulo affine passport.

NODE:
  Time-varying optical crowding from organelle trafficking and cytoplasmic
  streaming.

Step 9 method:
  4. Change the viewpoint.
"""

from __future__ import annotations

import cmath
import math

import numpy as np


NODE = "time-varying optical crowding from organelle trafficking and cytoplasmic streaming"

TRANSFER_ATTEMPTS = [
    "period holonomy must subtract time-varying crowding frame distortion",
    "period-domain class needs simultaneous reference-frame subtraction",
    "affine passport must include observation-frame history",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: time-varying optical crowding"]
    lines.append(
        "Constraint: the observed optical phase/intensity can drift because "
        "the measurement medium changes during acquisition, even when the "
        "underlying object is stationary."
    )
    t = np.linspace(0.0, 1.0, 400)
    true_phase = 0.7 * np.sin(2.0 * math.pi * t)
    crowding = 0.45 * np.sin(2.0 * math.pi * 3.0 * t + 0.4) + 0.20 * t
    reference = crowding + 0.015 * np.sin(2.0 * math.pi * 17.0 * t)
    observed = true_phase + crowding
    corrected = observed - reference
    raw_rmse = float(np.sqrt(np.mean((observed - true_phase) ** 2)))
    corrected_rmse = float(np.sqrt(np.mean((corrected - true_phase) ** 2)))
    apparent_drift = float(observed[-1] - observed[0])
    true_drift = float(true_phase[-1] - true_phase[0])
    lines.append(f"raw_rmse={raw_rmse:.6f} corrected_rmse={corrected_rmse:.6f}")
    lines.append(f"observed_endpoint_drift={apparent_drift:+.6f} true_endpoint_drift={true_drift:+.6f}")
    lines.append(
        "NODE verdict: a time-matched reference channel is needed; raw optical "
        "drift is not an invariant of the object."
    )
    return lines


def rectangle(center: complex, width: float, height: float, per_side: int) -> tuple[np.ndarray, np.ndarray]:
    x0 = center.real - width / 2.0
    x1 = center.real + width / 2.0
    y0 = center.imag - height / 2.0
    y1 = center.imag + height / 2.0
    points: list[complex] = []
    # Counter-clockwise rectangle, represented by segment midpoints and dz.
    corners = [complex(x0, y0), complex(x1, y0), complex(x1, y1), complex(x0, y1), complex(x0, y0)]
    mids: list[complex] = []
    dzs: list[complex] = []
    for a, b in zip(corners[:-1], corners[1:]):
        for k in range(per_side):
            u0 = k / per_side
            u1 = (k + 1) / per_side
            z0 = a + (b - a) * u0
            z1 = a + (b - a) * u1
            mids.append((z0 + z1) / 2.0)
            dzs.append(z1 - z0)
    return np.asarray(mids, dtype=complex), np.asarray(dzs, dtype=complex)


def source_form(z: complex, pole: complex) -> complex:
    return 1.0 / (z - pole)


def gauge_derivative(z: complex) -> complex:
    # d(phi) for phi(z)=z^2 + 0.35 exp(i z / 2), evaluated as coefficient
    # multiplying dz.
    return 2.0 * z + 0.35j * cmath.exp(0.5j * z)


def crowding_amplitudes(n: int, amp: float, phase: float) -> np.ndarray:
    k = np.arange(n, dtype=float)
    return 1.0 + amp * np.sin(2.0 * math.pi * k / n + phase) + 0.35 * amp * (k / max(1.0, n - 1.0))


def integrate(
    center: complex,
    pole: complex | None,
    amp: float,
    phase: float,
    reference_amp: float | None = None,
    per_side: int = 90,
) -> tuple[complex, complex, complex]:
    mids, dzs = rectangle(center, width=2.0, height=2.0, per_side=per_side)
    a = crowding_amplitudes(len(mids), amp, phase)
    if reference_amp is None:
        reference_amp = amp
    aref = crowding_amplitudes(len(mids), reference_amp, phase)
    source = np.zeros(len(mids), dtype=complex)
    if pole is not None:
        source = np.asarray([source_form(z, pole) for z in mids], dtype=complex)
    gauge = np.asarray([gauge_derivative(z) for z in mids], dtype=complex)
    raw = np.sum((source + a * gauge) * dzs)
    ref = np.sum((aref * gauge) * dzs)
    corrected = raw - ref
    return raw, ref, corrected


def winding(integral: complex) -> complex:
    return integral / (2.0j * math.pi)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Static gauge invariance of a closed-loop integral is known and would "
        "reduce to standard cohomology. The minimal non-reducing transfer is "
        "time-varying observation frame: a gauge that changes during contour "
        "acquisition is not one static exact form."
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
        "Viewpoint change: from static gauge class to acquisition-history class. "
        "A period-domain holonomy observable must be invariant under a moving "
        "observation frame or carry a simultaneous reference-frame passport."
    )
    pole = 0.2 + 0.1j
    inside_center = 0.0 + 0.0j
    outside_center = 3.0 + 0.0j
    lines.append("case amp raw_winding corrected_winding mismatched_ref_winding raw_error corrected_error mismatch_error")
    for label, center, expected in [("inside", inside_center, 1.0), ("outside", outside_center, 0.0)]:
        for amp in [0.0, 0.10, 0.25, 0.50]:
            raw, ref, corrected = integrate(center, pole if label == "inside" else pole, amp, phase=0.7)
            raw_bad, ref_bad, corrected_bad = integrate(
                center,
                pole if label == "inside" else pole,
                amp,
                phase=0.7,
                reference_amp=0.75 * amp,
            )
            wr = winding(raw)
            wc = winding(corrected)
            wb = winding(corrected_bad)
            raw_err = abs(wr - expected)
            corr_err = abs(wc - expected)
            bad_err = abs(wb - expected)
            lines.append(
                f"{label:7s} {amp:.2f} "
                f"{wr.real:+.4f}{wr.imag:+.4f}i "
                f"{wc.real:+.4f}{wc.imag:+.4f}i "
                f"{wb.real:+.4f}{wb.imag:+.4f}i "
                f"{raw_err:.4e} {corr_err:.4e} {bad_err:.4e}"
            )
    lines.append(
        "Interpretation: raw winding can be dominated by moving-frame crowding; "
        "a simultaneous reference restores the cohomology class, while a "
        "mismatched reference leaves a residual false holonomy."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("Penrose R41: time-varying observation-frame gate for period holonomy")
    out.append("ResearchNode: #42 Period-domain route -> Master-1 holonomy modulo passport")
    out.append(f"NODE: {NODE}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
