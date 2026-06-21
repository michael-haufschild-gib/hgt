#!/usr/bin/env python3
"""THE-MACHINE tick: ventilation-limited combustion -> C1 oriented 2-form.

NODE:
  Ventilation constraints can shift combustion from premixed-like behavior
  toward diffusion-limited burning.

Consolidated target:
  C1 -- carrier is one oriented 2-form omega = dO wedge dphi.

STEP 9 method:
  4. Change the viewpoint.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np


NODE = "ventilation constraints can shift combustion from premixed-like behavior toward diffusion-limited burning"

TRANSFER_ATTEMPTS = [
    "ventilation constrained C1 carrier shifts from scalar magnitude to oriented two form",
    "C1 is diffusion limited phase interface not premixed scalar amplitude",
    "signed two form detects transport interface when scalar carrier fails",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_ventilation_rows() -> list[str]:
    """Small reaction-zone model for the NODE constraint."""
    x = np.linspace(0.0, 1.0, 900)
    fuel = np.exp(-0.5 * ((x - 0.34) / 0.16) ** 2)
    lines = ["STEP 6 NODE TEST: ventilation shifts a scalar burn model into an interface model"]
    lines.append(
        "Fuel vapor is fixed; oxygen penetration and mixing width shrink with ventilation. "
        "Premixed-like means reaction rate follows the fuel scalar. Diffusion-limited means "
        "reaction is concentrated at the fuel/oxygen interface."
    )
    lines.append("vent penetration width total_rate corr_rate_fuel interface_fraction centroid")
    for vent in [1.0, 0.65, 0.40, 0.25, 0.12, 0.06]:
        penetration = 0.18 + 0.66 * vent
        width = 0.035 + 0.18 * vent
        oxygen = 1.0 / (1.0 + np.exp(((1.0 - penetration) - x) / width))
        rate = fuel * oxygen
        grad_f = np.abs(np.gradient(fuel, x))
        grad_o = np.abs(np.gradient(oxygen, x))
        interface_weight = grad_f * grad_o
        hot = interface_weight >= np.quantile(interface_weight, 0.82)
        total = float(np.trapezoid(rate, x))
        corr = float(np.corrcoef(rate, fuel)[0, 1])
        interface_fraction = float(np.trapezoid(rate * hot, x) / (total + 1e-300))
        centroid = float(np.trapezoid(x * rate, x) / (total + 1e-300))
        lines.append(
            f"{vent:0.2f} {penetration:0.4f} {width:0.4f} {total:0.6f} "
            f"{corr:0.4f} {interface_fraction:0.4f} {centroid:0.4f}"
        )
    lines.append(
        "NODE verdict: as ventilation shrinks, total rate falls and the reaction centroid moves "
        "toward the vent/interface. The scalar fuel-following view weakens while the interface "
        "fraction rises, matching the constraint."
    )
    return lines


def first_primes(n: int) -> list[int]:
    out: list[int] = []
    candidate = 2
    while len(out) < n:
        ok = True
        for p in out:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            out.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return out


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite(s: complex, primes: list[int]) -> complex:
    total = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        total -= math.log(p) * q / (1.0 - q)
    return complex(total)


def zeta_zeros(max_t: float) -> list[complex]:
    zeros: list[complex] = []
    k = 1
    while True:
        rho = complex(mp.zetazero(k))
        if rho.imag > max_t + 10:
            break
        zeros.append(rho)
        k += 1
    return zeros


def zero_pole_surrogate(s: complex, zeros: list[complex]) -> complex:
    total = 0.0 + 0.0j
    for rho in zeros:
        if abs(s.imag - rho.imag) < 16.0:
            total += 1.0 / (s - rho)
    return total


@dataclass
class TwoFormMetrics:
    integral: float
    mean_abs: float
    pos_fraction: float
    scalar_mass: float
    scalar_tv: float


def two_form_metrics(
    sigmas: np.ndarray,
    ts: np.ndarray,
    kind: str,
    primes: list[int],
    zeros: list[complex],
    rng: np.random.Generator,
) -> TwoFormMetrics:
    p_field = np.zeros((len(sigmas), len(ts)), dtype=complex)
    h_field = np.zeros_like(p_field)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            s = complex(float(sigma), float(t))
            h_field[i, j] = gamma_part(s)
            if kind == "true":
                p_field[i, j] = dlog_zeta(s)
            elif kind == "finite":
                p_field[i, j] = dlog_finite(s, primes)
            elif kind == "random_phase":
                base = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p_field[i, j] = abs(base) * complex(math.cos(theta), math.sin(theta))
            elif kind == "zero_pole":
                p_field[i, j] = zero_pole_surrogate(s, zeros)
            else:
                raise ValueError(kind)

    o_field = np.log1p(np.abs(p_field))
    phi = np.angle(h_field + p_field)
    phi = np.unwrap(np.unwrap(phi, axis=1), axis=0)
    d_o_dsigma, d_o_dt = np.gradient(o_field, sigmas, ts, edge_order=2)
    d_phi_dsigma, d_phi_dt = np.gradient(phi, sigmas, ts, edge_order=2)
    omega = d_o_dsigma * d_phi_dt - d_o_dt * d_phi_dsigma
    area = (sigmas[-1] - sigmas[0]) * (ts[-1] - ts[0])
    integral = float(np.mean(omega) * area)
    mean_abs = float(np.mean(np.abs(omega)))
    pos_fraction = float(np.mean(omega > 0))
    scalar_mass = float(np.mean(o_field))
    scalar_tv = float(np.mean(np.abs(d_o_dsigma)) + np.mean(np.abs(d_o_dt)))
    return TwoFormMetrics(integral, mean_abs, pos_fraction, scalar_mass, scalar_tv)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Ventilation Damkohler/mixing formulas do not apply unchanged to C1. "
        "The minimal transfer keeps only the NODE distinction: scalar bulk-rate view versus "
        "oriented interface/transport view."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):0.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 4: CHANGE THE VIEWPOINT")
    lines.append(
        "Old viewpoint: inspect scalar mass O=log(1+|P|). New viewpoint: inspect the oriented "
        "interface form dO∧dphi with phi=arg(Gamma_infty+P)."
    )

    rng = np.random.default_rng(2606213431)
    primes = first_primes(160)
    zeros = zeta_zeros(180.0)
    cases = [
        ("zero_strip", np.linspace(0.22, 0.92, 25), np.linspace(14.5, 84.0, 180)),
        ("critical_mid", np.linspace(0.22, 0.92, 25), np.linspace(100.0, 170.0, 180)),
        ("right_side", np.linspace(1.05, 1.55, 21), np.linspace(100.0, 170.0, 160)),
    ]
    kinds = ["true", "finite", "random_phase", "zero_pole"]
    lines.append(
        "case kind integral mean_abs pos_fraction scalar_mass scalar_tv sign old_scalar_rank"
    )
    for label, sigmas, ts in cases:
        metrics = {}
        for kind in kinds:
            metrics[kind] = two_form_metrics(sigmas, ts, kind, primes, zeros, rng)
        scalar_rank = {
            kind: rank
            for rank, (kind, _) in enumerate(
                sorted(metrics.items(), key=lambda kv: kv[1].scalar_mass, reverse=True), 1
            )
        }
        for kind in kinds:
            m = metrics[kind]
            sign = "+" if m.integral > 0 else "-" if m.integral < 0 else "0"
            lines.append(
                f"{label:12s} {kind:12s} {m.integral:+.6e} {m.mean_abs:.6e} "
                f"{m.pos_fraction:.4f} {m.scalar_mass:.6e} {m.scalar_tv:.6e} "
                f"{sign:1s} {scalar_rank[kind]:d}"
            )
        true_sign = math.copysign(1.0, metrics["true"].integral)
        zero_same = math.copysign(1.0, metrics["zero_pole"].integral) == true_sign
        lines.append(
            f"{label:12s} audit zero_pole_same_sign_as_true={int(zero_same)} "
            f"finite_opposes_true={int(metrics['true'].integral * metrics['finite'].integral < 0)} "
            f"random_opposes_true={int(metrics['true'].integral * metrics['random_phase'].integral < 0)}"
        )
    lines.append(
        "\nProvisional interpretation: C1 can only survive this transfer if the signed 2-form "
        "separates true from finite/random and is not reproduced by the correct-zero surrogate. "
        "Scalar O-ranks are reported to catch cases where the old premixed/scalar viewpoint already "
        "explains the outcome."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: ventilation-limited combustion -> C1 oriented 2-form")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 9/32 C1 oriented 2-form")
    out.extend(node_ventilation_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
