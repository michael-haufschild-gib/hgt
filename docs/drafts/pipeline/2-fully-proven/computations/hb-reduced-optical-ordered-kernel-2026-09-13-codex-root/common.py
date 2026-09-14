#!/usr/bin/env python3
"""Exact scalar coefficient from HB-TWO-SIDED-SOURCE-CURRENT, equations (13)-(14)."""

from __future__ import annotations

import cmath
import math


def _pow_pos(x: float, z: complex) -> complex:
    return cmath.exp(z * math.log(x))


def _F11(q: float, L: float, d: float) -> float:
    return -1 / (3 * q**3) + (L + d) / (4 * q**4) - L * d / (5 * q**5)


def _F21(q: float, L: float, d: float) -> float:
    return (
        -1 / (3 * q**3)
        + (2 * L + d) / (4 * q**4)
        - (L * L + 2 * L * d) / (5 * q**5)
        + L * L * d / (6 * q**6)
    )


def _F31(q: float, L: float, d: float) -> float:
    return (
        -1 / (2 * q**2)
        + (3 * L + d) / (3 * q**3)
        - (3 * L * L + 3 * L * d) / (4 * q**4)
        + (L**3 + 3 * L * L * d) / (5 * q**5)
        - L**3 * d / (6 * q**6)
    )


def _primitive_difference(F, L: float, d: float) -> float:
    q_plus = d + 1.0
    q_minus = max(L, d - 1.0)
    return F(q_plus, L, d) - F(q_minus, L, d)


def ordered_terms(
    rho: complex,
    L: float,
    x: float,
    *,
    onset: bool = True,
    endpoint: str = "difference",
) -> tuple[complex, complex]:
    """Return the two terms whose difference is the exact equation-(14) coefficient.

    x parametrizes the complete optical cross-section by
    d=(L-1)+x*L, 0<=x<=1.  endpoint supports hostile boundary ablations.
    """
    d = (L - 1.0) + x * L
    delta = 2.0 * rho - 1.0
    s = rho - 2.0
    t = -rho - 1.0
    eta_s = (2.0 * s + 1.0) * (2.0 * s + 2.0)
    eta_t = (2.0 * t + 1.0) * (2.0 * t + 2.0)
    k_s = s * (s - 1.0) / 4.0
    k_t = t * (t - 1.0) / 4.0

    def bracket(F):
        q_plus = d + 1.0
        q_minus = max(L, d - 1.0)
        if endpoint == "difference":
            return F(q_plus, L, d) - F(q_minus, L, d)
        if endpoint == "plus":
            return F(q_plus, L, d)
        if endpoint == "minus":
            return -F(q_minus, L, d)
        raise ValueError(endpoint)

    f11 = bracket(_F11)
    f21 = bracket(_F21)
    f31 = bracket(_F31) if onset else 0.0
    k_st = eta_s * (eta_t * f11 - 36.0 * k_t * f21 + 12.0 * k_t * delta / L * f31)
    k_ts = eta_t * (eta_s * f11 - 36.0 * k_s * f21 - 12.0 * k_s * delta / L * f31)
    return _pow_pos(L, delta) * k_st, _pow_pos(L, -delta) * k_ts


def coefficient(rho: complex, L: float, x: float, **kwargs) -> complex:
    a, b = ordered_terms(rho, L, x, **kwargs)
    return a - b


def relative_residual(rho: complex, L: float, x: float, **kwargs) -> float:
    a, b = ordered_terms(rho, L, x, **kwargs)
    return abs(a - b) / max(abs(a) + abs(b), 1e-300)

