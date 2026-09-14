#!/usr/bin/env python3
"""Exact critical-line angular pairing surviving physical horizon current+contact."""

from __future__ import annotations

import math
import pathlib
import sys

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
PRIOR = HERE.parent / "hb-signed-native-delay-bulk-2026-09-13-codex-root"
sys.path.insert(0, str(PRIOR))

from native_delay import completed_lambda_data, gl, scalar_jets  # noqa: E402


def angular_pair_terms(gamma, x, y, principal=False, margin=40, dps=35):
    f, fx, fy, fxx, fxy, _, _, _ = scalar_jets(
        gamma, x, y, margin, dps, principal, reduce_point=False
    )
    mu = -(gamma * gamma + 0.25)
    j0, j1 = f * fy, -f * fx
    k0 = (
        y * (fx * fx + fy * fy)
        + y * y * (fx * fxy - fy * fxx)
        + mu * f * fy
    )
    k1 = -y * y * (fx * fxx + fy * fxy)
    square = (2 * mu - 2) * (j0 * j0 + j1 * j1)
    gradient = 2 * (j0 * k0 + j1 * k1)
    return np.asarray((square, gradient, square + gradient), dtype=np.complex128)


def principal_factor(gamma, phase):
    """Closed principal-cusp angular pair at phase arg(A)+gamma*log(y)."""
    c, s = math.cos(phase), math.sin(phase)
    p = c - 2 * gamma * s
    return -8 * c * p * p * ((2 * gamma * gamma + 1) * c + gamma * s)


def cell_remainder(gamma, ymax=4.0, x_order=14, y_order=14, margin=40, dps=35):
    """Integral over truncated modular cell of full minus principal pairing."""

    def x_integrand(x):
        lower = math.sqrt(max(0.0, 1 - x * x))
        cuts = sorted(set([lower, ymax] + [q for q in (1.2, 1.7, 2.5) if lower < q < ymax]))
        total = np.zeros(5, dtype=np.complex128)
        for lo, hi in zip(cuts, cuts[1:]):
            def y_integrand(y):
                full = angular_pair_terms(gamma, x, y, False, margin, dps)
                principal = angular_pair_terms(gamma, x, y, True, margin, dps)
                diff = full - principal
                return np.asarray(
                    (diff[0], diff[1], diff[2], abs(full[2]) + abs(principal[2]), abs(diff[2])),
                    dtype=np.complex128,
                )

            total += gl(y_integrand, lo, hi, y_order)
        return total

    out = gl(x_integrand, -0.5, 0.5, x_order)
    _, log_abs = completed_lambda_data(float(gamma), int(dps))
    return {
        "square_remainder": float(out[0].real),
        "gradient_remainder": float(out[1].real),
        "total_remainder": float(out[2].real),
        "imaginary_leak": float(abs(out[2].imag)),
        "full_principal_l1_budget": float(out[3].real),
        "remainder_l1": float(out[4].real),
        "component_cancellation": float(abs(out[2]) / max(abs(out[0]) + abs(out[1]), 1e-300)),
        "relative_to_source_budget": float(abs(out[2]) / max(out[3].real, 1e-300)),
        "physical_logabs": float(math.log(max(abs(out[2]), 1e-300)) + 4 * log_abs),
    }

