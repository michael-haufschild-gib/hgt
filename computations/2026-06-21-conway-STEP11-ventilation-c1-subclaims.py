#!/usr/bin/env python3
"""STEP 11 for ventilation -> C1: split the signed-form claim into subclaims.

Subclaims:
  A. A chosen O/phi definition gives a stable signed 2-form for true data.
  B. finite/random surrogates have the opposite sign.
  C. correct-zero surrogate does not reproduce the true sign.
  D. the form vanishes or sharply collapses on sigma > 1.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-ventilation-c1-twoform.py")

first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]
zeta_zeros = BASE["zeta_zeros"]
zero_pole_surrogate = BASE["zero_pole_surrogate"]


def build_fields(sigmas, ts, kind, primes, zeros, rng):
    a = np.zeros((len(sigmas), len(ts)), dtype=complex)
    p = np.zeros_like(a)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            s = complex(float(sigma), float(t))
            a[i, j] = gamma_part(s)
            if kind == "true":
                p[i, j] = dlog_zeta(s)
            elif kind == "finite":
                p[i, j] = dlog_finite(s, primes)
            elif kind == "random_phase":
                base = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p[i, j] = abs(base) * complex(math.cos(theta), math.sin(theta))
            elif kind == "zero_pole":
                p[i, j] = zero_pole_surrogate(s, zeros)
            else:
                raise ValueError(kind)
    return a, p


def variant_integral(sigmas, ts, a, p, o_kind, phi_kind):
    h = a + p
    if o_kind == "P":
        o = np.log1p(np.abs(p))
    elif o_kind == "H":
        o = np.log1p(np.abs(h))
    elif o_kind == "defect":
        o = np.maximum(np.log(np.abs(a) + 1e-300), np.log(np.abs(p) + 1e-300)) - np.log(
            np.abs(h) + 1e-300
        )
    else:
        raise ValueError(o_kind)

    if phi_kind == "H":
        phi = np.angle(h)
    elif phi_kind == "P":
        phi = np.angle(p)
    elif phi_kind == "ratio":
        phi = np.angle(p / (a + 1e-300))
    else:
        raise ValueError(phi_kind)

    phi = np.unwrap(np.unwrap(phi, axis=1), axis=0)
    d_o_dsigma, d_o_dt = np.gradient(o, sigmas, ts, edge_order=2)
    d_phi_dsigma, d_phi_dt = np.gradient(phi, sigmas, ts, edge_order=2)
    omega = d_o_dsigma * d_phi_dt - d_o_dt * d_phi_dsigma
    area = (sigmas[-1] - sigmas[0]) * (ts[-1] - ts[0])
    return float(np.mean(omega) * area), float(np.mean(np.abs(omega)))


def sign(x: float) -> int:
    return 1 if x > 0 else -1 if x < 0 else 0


def main() -> None:
    rng = np.random.default_rng(2606213601)
    primes = first_primes(160)
    zeros = zeta_zeros(180.0)
    cases = {
        "zero_strip": (np.linspace(0.22, 0.92, 23), np.linspace(14.5, 84.0, 150)),
        "critical_mid": (np.linspace(0.22, 0.92, 23), np.linspace(100.0, 170.0, 150)),
        "right_side": (np.linspace(1.05, 1.55, 19), np.linspace(100.0, 170.0, 130)),
    }
    kinds = ["true", "finite", "random_phase", "zero_pole"]
    variants = [(o, phi) for o in ["P", "H", "defect"] for phi in ["H", "P", "ratio"]]

    print("STEP 11 C1 subclaim battery")
    print("method=1 split into subclaims")
    print("variant O_kind phi_kind zero_true finite random zero_pole right_true gate")

    fields = {}
    for case, (sigmas, ts) in cases.items():
        fields[case] = {}
        for kind in kinds:
            fields[case][kind] = build_fields(sigmas, ts, kind, primes, zeros, rng)

    pass_count = 0
    for o_kind, phi_kind in variants:
        vals = {}
        for case, (sigmas, ts) in cases.items():
            vals[case] = {}
            for kind in kinds:
                a, p = fields[case][kind]
                vals[case][kind] = variant_integral(sigmas, ts, a, p, o_kind, phi_kind)
        z_true = vals["zero_strip"]["true"][0]
        c_true = vals["critical_mid"]["true"][0]
        c_finite = vals["critical_mid"]["finite"][0]
        c_random = vals["critical_mid"]["random_phase"][0]
        c_zero = vals["critical_mid"]["zero_pole"][0]
        r_true = vals["right_side"]["true"][0]
        right_collapse = abs(r_true) < 0.15 * max(abs(c_true), 1e-12)
        gate = (
            sign(z_true) == sign(c_true)
            and sign(c_true) != sign(c_finite)
            and sign(c_true) != sign(c_random)
            and sign(c_true) != sign(c_zero)
            and right_collapse
        )
        pass_count += int(gate)
        print(
            f"{o_kind:7s} {phi_kind:5s} {z_true:+.4e} {c_true:+.4e} "
            f"{c_finite:+.4e} {c_random:+.4e} {c_zero:+.4e} {r_true:+.4e} {int(gate)}"
        )
    print()
    print(f"C1_VARIANTS_PASS_FULL_SUBCLAIM_GATE {pass_count}/{len(variants)}")
    print(
        "Interpretation: a C1 definition must pass all four subclaims, not just produce a nonzero "
        "or visually signed form. Variants failing by zero-pole sign reduce toward zero geometry; "
        "variants failing by finite/random sign are not native; variants failing right-collapse are "
        "not seam-localized."
    )


if __name__ == "__main__":
    main()
