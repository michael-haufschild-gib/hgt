#!/usr/bin/env python3
"""THE-MACHINE tick: Grote-Hynes memory friction -> C4.

NODE:
  Grote-Hynes corrections may be needed when friction has memory.

Consolidated target:
  12/32 C4 -- cross-lane correlation length.

STEP 9 method:
  19. Write the fake proof.
"""

from __future__ import annotations

import math
import runpy
from dataclasses import dataclass

import numpy as np


NODE = "Grote-Hynes corrections may be needed when friction has memory"
TARGET = "12/32 C4 cross-lane correlation"
METHOD = "19. Write the fake proof"

TRANSFER_ATTEMPTS = [
    "Grote-Hynes memory friction becomes a cross-lane sigma memory kernel for C4",
    "frequency dependent friction correction becomes frequency dependent xi_sigma",
    "a scalar lane correlation length is insufficient when cross-sigma memory has shape",
]


BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
first_primes = BASE["first_primes"]
build_fields = BASE["build_fields"]
lane_standardize = BASE["lane_standardize"]
circular_shift_lanes = BASE["circular_shift_lanes"]
fourier_scramble_lanes = BASE["fourier_scramble_lanes"]
corr_metrics = BASE["corr_metrics"]
lane_power_rel_diff = BASE["lane_power_rel_diff"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def markov_lambda(omega_b: float, gamma: float) -> float:
    return float((-gamma + math.sqrt(gamma * gamma + 4.0 * omega_b * omega_b)) / 2.0)


def gh_lambda_exponential_memory(omega_b: float, gamma: float, tau: float) -> float:
    """Positive Grote-Hynes root for K(t)=gamma/tau exp(-t/tau).

    The dimensionless root solves
        lambda^2 + lambda * gamma/(1 + lambda*tau) = omega_b^2.
    Tau=0 collapses to Markov friction.
    """

    if abs(tau) < 1e-14:
        return markov_lambda(omega_b, gamma)
    coeff = [tau, 1.0, gamma - tau * omega_b * omega_b, -omega_b * omega_b]
    roots = np.roots(coeff)
    candidates = sorted(
        float(r.real) for r in roots if abs(float(r.imag)) < 1e-9 and float(r.real) > 0.0
    )
    if not candidates:
        raise RuntimeError(f"no positive GH root for omega={omega_b} gamma={gamma} tau={tau}")
    return candidates[-1]


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: memory friction is not scalar friction"]
    lines.append(
        "Constraint: with exponential bath memory, the escape prefactor is fixed by the "
        "frequency-dependent friction gamma_hat(lambda), not only by integrated gamma."
    )
    lines.append("omega gamma tau omega_tau lambda_markov lambda_GH kappa_markov kappa_GH rel_rate_lift")
    for omega in [0.7, 1.0, 1.6]:
        for gamma in [0.4, 1.5, 5.0]:
            lam_m = markov_lambda(omega, gamma)
            for tau in [0.0, 0.05 / omega, 0.25 / omega, 1.0 / omega, 4.0 / omega]:
                lam_gh = gh_lambda_exponential_memory(omega, gamma, tau)
                rel = (lam_gh - lam_m) / (lam_m + 1e-300)
                lines.append(
                    f"{omega:.2f} {gamma:.2f} {tau:.5f} {omega*tau:.3f} "
                    f"{lam_m:.6f} {lam_gh:.6f} {lam_m/omega:.6f} {lam_gh/omega:.6f} {rel:+.6f}"
                )
    lines.append(
        "NODE verdict: tau=0 collapses to Kramers/Markov. At fixed integrated friction, "
        "memory can change the prefactor by order-one factors when omega_b*tau is not small."
    )
    return lines


def positive_lane_kernel(field: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    x = lane_standardize(field)
    corr = x.T @ x / x.shape[0]
    np.fill_diagonal(corr, 0.0)
    by_dist = []
    for d in range(1, corr.shape[0]):
        by_dist.append(float(np.mean([corr[i, i + d] for i in range(corr.shape[0] - d)])))
    signed = np.asarray(by_dist, dtype=float)
    return signed, np.maximum(signed, 0.0)


def lambda_from_discrete_kernel(omega: float, kernel: np.ndarray) -> float:
    gamma0 = float(np.sum(kernel))
    if gamma0 <= 1e-14:
        return omega

    dists = np.arange(1.0, len(kernel) + 1.0)

    def f(lam: float) -> float:
        khat = float(np.sum(kernel * np.exp(-lam * dists)))
        return lam * lam + lam * khat - omega * omega

    lo = 0.0
    hi = max(omega + gamma0 + 2.0, 2.0)
    while f(hi) <= 0.0:
        hi *= 2.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if f(mid) <= 0.0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


@dataclass
class MemoryMetrics:
    gamma0: float
    xi: float
    tail_frac: float
    top_eig: float
    markov_lam: float
    memory_lam: float
    lift: float
    curve_area: float
    kernel: np.ndarray
    signed: np.ndarray


def memory_metrics(field: np.ndarray, omega: float = 1.0) -> MemoryMetrics:
    signed, kernel = positive_lane_kernel(field)
    gamma0 = float(np.sum(kernel))
    if gamma0 <= 1e-14:
        xi = 0.0
        tail = 0.0
    else:
        dists = np.arange(1.0, len(kernel) + 1.0)
        xi = float(np.sum(dists * kernel) / gamma0)
        tail = float(np.sum(kernel[1:]) / gamma0)
    met = corr_metrics(lane_standardize(field))
    lam_m = markov_lambda(omega, gamma0)
    lam_mem = lambda_from_discrete_kernel(omega, kernel)
    probes = []
    for w in [0.35, 0.50, 0.75, 1.00, 1.50, 2.00, 3.00]:
        mm = markov_lambda(w, gamma0)
        gm = lambda_from_discrete_kernel(w, kernel)
        probes.append((gm - mm) / (mm + 1e-300))
    return MemoryMetrics(
        gamma0=gamma0,
        xi=xi,
        tail_frac=tail,
        top_eig=met.top_eig,
        markov_lam=lam_m,
        memory_lam=lam_mem,
        lift=(lam_mem - lam_m) / (lam_m + 1e-300),
        curve_area=float(np.trapezoid(probes, x=[0.35, 0.50, 0.75, 1.00, 1.50, 2.00, 3.00])),
        kernel=kernel,
        signed=signed,
    )


def same_mass_xi_counterexample_rows() -> list[str]:
    lines = ["\nSTEP 9 METHOD 19: FAKE PROOF AND GAP"]
    lines.append(
        "Fake proof: C4 would follow from a large scalar xi_sigma, because xi_sigma would "
        "summarize all cross-lane rigidity."
    )
    lines.append(
        "Gap exposed by the NODE: a memory correction depends on the full Laplace transform "
        "of the lane kernel, not only on mass and first moment."
    )
    k_a = np.asarray([0.5, 0.0, 0.0, 0.0, 0.5], dtype=float)
    k_b = np.asarray([0.0, 0.0, 1.0, 0.0, 0.0], dtype=float)
    rows = []
    for name, k in [("split_1_5", k_a), ("point_3", k_b)]:
        gamma0 = float(np.sum(k))
        dists = np.arange(1.0, len(k) + 1.0)
        xi = float(np.sum(dists * k) / gamma0)
        lam_m = markov_lambda(1.0, gamma0)
        lam_mem = lambda_from_discrete_kernel(1.0, k)
        rows.append((name, gamma0, xi, lam_m, lam_mem, (lam_mem - lam_m) / lam_m))
    lines.append("kernel gamma0 xi markov_lambda memory_lambda rel_lift")
    for row in rows:
        lines.append(f"{row[0]:9s} {row[1]:.3f} {row[2]:.3f} {row[3]:.6f} {row[4]:.6f} {row[5]:+.6f}")
    lines.append(
        "Same gamma0 and xi, different memory lift. Missing lemma: xi_sigma alone determines "
        "frequency-dependent C4 response. The lemma is false in this finite kernel model."
    )
    return lines


def bar(value: float, scale: float = 18.0) -> str:
    n = int(max(0.0, min(28.0, round(scale * value))))
    return "#" * n + "." * (28 - n)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "The Grote-Hynes molecular formula does not apply unchanged to C4: C4 has no "
        "molecular barrier, solvent friction, or Kramers rate. Direct use would be HT-blind."
    )
    lines.append(
        "Minimal transfer: keep only the constraint that scalar friction is insufficient "
        "when the coupling has memory. Replace bath memory by the positive cross-sigma "
        "correlation kernel of the phase-weld field."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.extend(same_mass_xi_counterexample_rows())
    lines.append("\nSTEP 9 C4 MEMORY-KERNEL EXPERIMENT")

    rng = np.random.default_rng(2606215111)
    primes = first_primes(160)
    cases = [
        ("critical_low", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 170.0), "critical"),
        ("critical_high", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 570.0), "critical"),
        ("right_low", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (100.0, 170.0), "right"),
        ("right_high", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (500.0, 570.0), "right"),
    ]
    lines.append(
        "case region kind power_diff top_eig gamma0 xi tail_frac markov_lam "
        "memory_lam rel_lift curve_area kernel verdict"
    )
    critical_true_separates = 0
    critical_total = 0
    right_true_finite_collapse = 0
    right_total = 0
    for label, sigmas, window, region in cases:
        fields = build_fields(sigmas, window, 240, primes, rng)
        true = lane_standardize(fields["true"])
        variants = {
            "true": true,
            "finite": lane_standardize(fields["finite"]),
            "random": lane_standardize(fields["random"]),
            "shifted": circular_shift_lanes(true, rng),
            "fourier": fourier_scramble_lanes(true, rng),
        }
        metrics = {name: memory_metrics(field) for name, field in variants.items()}
        true_m = metrics["true"]
        ctrl_max_lift = max(metrics[k].lift for k in ["finite", "random", "shifted", "fourier"])
        finite_lift_gap = abs(true_m.lift - metrics["finite"].lift)
        if region == "critical":
            ok = true_m.lift > ctrl_max_lift + 0.03 and true_m.tail_frac > 0.20
            critical_true_separates += int(ok)
            critical_total += 1
        else:
            ok = finite_lift_gap < 0.02
            right_true_finite_collapse += int(ok)
            right_total += 1
        for kind, m in metrics.items():
            pdiff = 0.0 if kind in {"true", "finite", "random"} else lane_power_rel_diff(true, variants[kind])
            verdict = ""
            if kind == "true":
                verdict = "critical_sep" if region == "critical" and ok else "right_collapse" if region == "right" and ok else "watch"
            kstr = ",".join(f"{x:.3f}" for x in m.kernel)
            lines.append(
                f"{label:13s} {region:8s} {kind:7s} {pdiff:.2e} {m.top_eig:.4f} "
                f"{m.gamma0:.4f} {m.xi:.4f} {m.tail_frac:.4f} {m.markov_lam:.6f} "
                f"{m.memory_lam:.6f} {m.lift:+.6f} {m.curve_area:+.6f} [{kstr}] {verdict}"
            )
    lines.append("")
    lines.append(f"CRITICAL_TRUE_MEMORY_SEPARATES {critical_true_separates}/{critical_total}")
    lines.append(f"RIGHT_TRUE_FINITE_MEMORY_COLLAPSE {right_true_finite_collapse}/{right_total}")

    lines.append("\nSTEP 11 WILD METAPHOR EXPERIMENT: barrier-frequency scan")
    lines.append(
        "Metaphor: C4 is not just a rigid rod across sigma-lanes; it is a bath with memory. "
        "Probe it with fictitious barrier frequencies and draw the relative memory lift curve."
    )
    lines.append("case kind curve")
    for label, sigmas, window, _region in cases[:3]:
        fields = build_fields(sigmas, window, 180, primes, rng)
        variants = {
            "true": lane_standardize(fields["true"]),
            "finite": lane_standardize(fields["finite"]),
            "random": lane_standardize(fields["random"]),
        }
        for kind, field in variants.items():
            _, kernel = positive_lane_kernel(field)
            vals = []
            for w in [0.35, 0.50, 0.75, 1.00, 1.50, 2.00, 3.00]:
                mm = markov_lambda(w, float(np.sum(kernel)))
                gm = lambda_from_discrete_kernel(w, kernel)
                vals.append((gm - mm) / (mm + 1e-300))
            curve = " ".join(f"{v:+.3f}" for v in vals)
            lines.append(f"{label:13s} {kind:7s} {bar(float(np.trapezoid(vals)))} {curve}")
    lines.append(
        "Interpretation: if the critical true curve separates while right-side true/finite "
        "collapse, C4 needs a full cross-lane memory-kernel gate. A scalar xi_sigma gate is "
        "a fake-proof gap, not a complete discriminator."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: Grote-Hynes memory friction -> C4")
    out.append(f"NODE: {NODE}")
    out.append(f"Standing-order target: {TARGET}")
    out.append(f"STEP 9 method: {METHOD}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
