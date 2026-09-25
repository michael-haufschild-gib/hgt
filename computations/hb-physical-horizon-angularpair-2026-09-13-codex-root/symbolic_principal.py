#!/usr/bin/env python3
"""Exact rational-polynomial derivation of the principal-cusp pairing."""

from __future__ import annotations

import json
import os

import math
from fractions import Fraction


# Sparse polynomials in (gamma, cos(u), sin(u)).
def const(value):
    value = Fraction(value)
    return {} if value == 0 else {(0, 0, 0): value}


def var(index):
    exponent = [0, 0, 0]
    exponent[index] = 1
    return {tuple(exponent): Fraction(1)}


def add(*terms):
    out = {}
    for term in terms:
        for monomial, coefficient in term.items():
            out[monomial] = out.get(monomial, Fraction(0)) + coefficient
            if out[monomial] == 0:
                del out[monomial]
    return out


def scale(value, term):
    value = Fraction(value)
    return {key: value * coefficient for key, coefficient in term.items() if value * coefficient}


def mul(*terms):
    out = const(1)
    for term in terms:
        nxt = {}
        for left, a in out.items():
            for right, b in term.items():
                key = tuple(left[j] + right[j] for j in range(3))
                nxt[key] = nxt.get(key, Fraction(0)) + a * b
        out = {key: value for key, value in nxt.items() if value}
    return out


def power(term, exponent):
    return mul(*([term] * exponent)) if exponent else const(1)


gamma, cosine, sine = var(0), var(1), var(2)
p = add(cosine, scale(-2, mul(gamma, sine)))
mu = add(scale(-1, power(gamma, 2)), const(Fraction(-1, 4)))
j = scale(2, mul(cosine, p))
k = add(power(p, 2), scale(2, mul(mu, cosine, p)))
direct = add(mul(add(scale(2, mu), const(-2)), power(j, 2)), scale(2, mul(j, k)))
factored = scale(-8, mul(
    cosine,
    power(p, 2),
    add(mul(add(scale(2, power(gamma, 2)), const(1)), cosine), mul(gamma, sine)),
))
identity_residual = add(direct, scale(-1, factored))


def even_phase_moment(cosine_power, sine_power):
    if cosine_power % 2 or sine_power % 2:
        return Fraction(0)
    m, n = cosine_power // 2, sine_power // 2
    return Fraction(
        math.factorial(2 * m) * math.factorial(2 * n),
        4 ** (m + n) * math.factorial(m) * math.factorial(n) * math.factorial(m + n),
    )


phase_mean = {}
for (g_power, c_power, s_power), coefficient in factored.items():
    value = coefficient * even_phase_moment(c_power, s_power)
    phase_mean[g_power] = phase_mean.get(g_power, Fraction(0)) + value
phase_mean = {key: value for key, value in phase_mean.items() if value}
expected_mean = {4: Fraction(-8), 2: Fraction(-6), 0: Fraction(-3)}
mean_residual = add(
    {(key, 0, 0): value for key, value in phase_mean.items()},
    scale(-1, {(key, 0, 0): value for key, value in expected_mean.items()}),
)
payload = {
    "factored": "-8*cos(u)*(cos(u)-2*gamma*sin(u))^2*((2*gamma^2+1)*cos(u)+gamma*sin(u))",
    "identity_residual_terms": len(identity_residual),
    "phase_mean_coefficients": {str(key): str(value) for key, value in sorted(phase_mean.items())},
    "mean_residual_terms": len(mean_residual),
    "phase_mean": "-(8*gamma^4+6*gamma^2+3)",
    "strict_sign_for_real_gamma": "negative for every real gamma",
}
with open("symbolic-principal.json.tmp", "w") as handle:
    json.dump(payload, handle, indent=2)
os.replace("symbolic-principal.json.tmp", "symbolic-principal.json")
