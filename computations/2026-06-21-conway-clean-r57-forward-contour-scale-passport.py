#!/usr/bin/env python3
"""Clean Finding 57 candidate: scale decomposition for forward contour moments.

ResearchNode:
    GPT topic #6, forward contour moments:
        M_k(R) = (1/2 pi i) int_{dR} (s-1/2)^k xi'/xi ds
               = sum_{rho in R} (rho-1/2)^k.

Random NODE:
    In chemical master equations, volume scaling affects both molecule numbers
    and propensity constants, not only the noise magnitude.

NODE constraint:
    A scale change is not one scalar "noise" parameter. It changes how many
    discrete objects are present and how the event rates/weights are computed.

STEP 8 transfer options:
    A_scale_decompose_normalized_Mk: nested contour scale changes both source
      membership and normalized moment weights.
    B_volume_as_guard_band: contour guard bands are molecule-volume buffers.
    C_propensity_as_side_quadrature_rate: side sampling rates act as propensities.

Continue with A. It is the minimal change and directly targets forward contour
moments rather than generic detector noise.

STEP 9 method #4:
    Change the viewpoint. View nested contour rescaling not as "same moment with
    smaller numerical noise", but as a coupled source-membership plus moment-
    weight transformation.
"""

from __future__ import annotations

import cmath
import math
from dataclasses import dataclass

import numpy as np


def cme_volume_validation() -> None:
    print("NODE validation: CME volume scaling changes counts and propensities")
    print("Omega count_A correct_birth correct_dimer naive_dimer naive/correct")
    concentration = 4.0
    k_birth = 0.7
    k_dimer = 0.1
    for omega in [10, 40, 160]:
        x = int(round(concentration * omega))
        correct_birth = k_birth * omega
        correct_dimer = k_dimer * x * (x - 1) / (2.0 * omega)
        naive_dimer = k_dimer * x * (x - 1) / 2.0
        print(
            f"{omega:5d} {x:7d} {correct_birth:13.3f} "
            f"{correct_dimer:13.3f} {naive_dimer:12.3f} "
            f"{naive_dimer / correct_dimer:13.1f}"
        )
    print(
        "Interpretation: treating volume as noise-only misses the count scaling "
        "and the volume factor in bimolecular propensities."
    )


def quartet(a: float, gamma: float) -> list[complex]:
    return [
        complex(a, gamma),
        complex(-a, gamma),
        complex(a, -gamma),
        complex(-a, -gamma),
    ]


def seam_pair(gamma: float) -> list[complex]:
    return [complex(0.0, gamma), complex(0.0, -gamma)]


ZEROS = (
    quartet(0.12, 0.80)
    + seam_pair(1.30)
    + quartet(0.20, 1.80)
    + seam_pair(2.40)
)


def dlog_poly(z: complex) -> complex:
    return sum(1.0 / (z - root) for root in ZEROS)


def square_boundary(half_width: float, samples_per_side: int) -> tuple[np.ndarray, np.ndarray]:
    """Return midpoint samples z and dz on a counterclockwise square."""

    h = half_width
    n = samples_per_side
    pts: list[complex] = []
    dzs: list[complex] = []
    sides = [
        (complex(-h, -h), complex(h, -h)),
        (complex(h, -h), complex(h, h)),
        (complex(h, h), complex(-h, h)),
        (complex(-h, h), complex(-h, -h)),
    ]
    for start, end in sides:
        step = (end - start) / n
        for i in range(n):
            pts.append(start + (i + 0.5) * step)
            dzs.append(step)
    return np.asarray(pts, dtype=complex), np.asarray(dzs, dtype=complex)


def enclosed_indices(half_width: float) -> set[int]:
    return {
        i
        for i, root in enumerate(ZEROS)
        if max(abs(root.real), abs(root.imag)) < half_width
    }


def exact_moment(indices: set[int], k: int) -> complex:
    return sum(ZEROS[i] ** k for i in indices)


def contour_moment(half_width: float, k: int, samples_per_side: int = 900) -> complex:
    z, dz = square_boundary(half_width, samples_per_side)
    vals = np.array([(zz**k) * dlog_poly(zz) for zz in z], dtype=complex)
    return complex(np.sum(vals * dz) / (2j * math.pi))


@dataclass(frozen=True)
class ScaleRow:
    scale: float
    count: int
    normalized: complex
    total_delta: complex
    retained_reweighting: complex
    new_source_influx: complex


def normalized_rows(k: int, scales: list[float]) -> list[ScaleRow]:
    rows: list[ScaleRow] = []
    prev_scale: float | None = None
    prev_indices: set[int] = set()
    prev_normalized = 0.0 + 0.0j
    for scale in scales:
        indices = enclosed_indices(scale)
        normalized = exact_moment(indices, k) / (scale**k if k else 1.0)
        if prev_scale is None:
            total_delta = 0.0 + 0.0j
            retained = 0.0 + 0.0j
            influx = normalized
        else:
            retained = sum(
                ZEROS[i] ** k / (scale**k if k else 1.0)
                - ZEROS[i] ** k / (prev_scale**k if k else 1.0)
                for i in prev_indices
            )
            influx = sum(ZEROS[i] ** k / (scale**k if k else 1.0) for i in indices - prev_indices)
            total_delta = normalized - prev_normalized
        rows.append(ScaleRow(scale, len(indices), normalized, total_delta, retained, influx))
        prev_scale = scale
        prev_indices = indices
        prev_normalized = normalized
    return rows


def contour_transfer() -> None:
    scales = [1.00, 1.40, 2.00, 2.60]

    print("\nForward contour check on a completed symmetric toy divisor")
    print("scale k count exact.real contour.real abs_error")
    for scale in scales:
        indices = enclosed_indices(scale)
        for k in [0, 2, 4]:
            exact = exact_moment(indices, k)
            approx = contour_moment(scale, k)
            print(
                f"{scale:4.2f} {k:d} {len(indices):5d} "
                f"{exact.real:11.6f} {approx.real:12.6f} {abs(approx - exact):9.2e}"
            )

    print("\nScale-decomposition passport for normalized moments N_k(L)=M_k(L)/L^k")
    print("k scale count N.real delta.real retained.real influx.real cancellation_ratio")
    for k in [0, 2, 4]:
        for row in normalized_rows(k, scales):
            denom = abs(row.retained_reweighting.real) + abs(row.new_source_influx.real)
            cancellation = abs(row.total_delta.real) / denom if denom else 1.0
            print(
                f"{k:d} {row.scale:4.2f} {row.count:5d} "
                f"{row.normalized.real:8.4f} {row.total_delta.real:10.4f} "
                f"{row.retained_reweighting.real:13.4f} {row.new_source_influx.real:11.4f} "
                f"{cancellation:18.4f}"
            )

    print(
        "\nInterpretation: nested forward moments must deaggregate contour-scale "
        "changes into retained-source reweighting and new-source influx. A small "
        "change in normalized M_k can be cancellation between those two effects, "
        "not evidence that the contour moment is scale-invariant or noise-stable."
    )


def main() -> None:
    cme_volume_validation()
    contour_transfer()


if __name__ == "__main__":
    main()
