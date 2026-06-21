#!/usr/bin/env python3
"""THE-MACHINE tick: observation sequence formalization -> two-clock layer.

NODE:
  Bayesian updating still requires a defined observation sequence; ambiguous,
  interactive, or agent-dependent data streams need extra formalization.

Consolidated target:
  30/32 Two-Clock Layer.

STEP 9 method:
  16. Use a minimal counterexample.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = (
    "Bayesian updating still requires a defined observation sequence; ambiguous, "
    "interactive, or agent-dependent data streams need extra formalization"
)
TARGET = "30/32 Two-Clock Layer"
METHOD = "16. Use a minimal counterexample"

TRANSFER_ATTEMPTS = [
    "two-clock evidence needs an explicit observation sequence before updating the sign",
    "finite-prime gate and analytic tension are ambiguous data streams until sequenced",
    "agent-dependent sampling can flip a two-clock seam statistic unless counterexample-free",
]


C4 = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
gamma_part = C4["gamma_part"]
dlog_zeta = C4["dlog_zeta"]
dlog_finite = C4["dlog_finite"]
first_primes = C4["first_primes"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def logit(p: float) -> float:
    return math.log(p / (1.0 - p))


def inv_logit(x: float) -> float:
    return 1.0 / (1.0 + math.exp(-x))


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: updating requires a data stream"]
    lines.append(
        "Constraint: if the next observation channel is chosen by an agent/policy, a posterior "
        "is not defined by the multiset of possible observations alone."
    )
    prior = 0.5
    # Observation A has likelihood ratio 3 for result +. Channel B+ confirms positives;
    # channel B- is an adversarial/negative follow-up. Same first datum, different defined
    # second observation sequence, different posterior.
    first_lr = 3.0
    confirm_lr = 4.0
    adversarial_lr = 0.35
    posterior_after_a = inv_logit(logit(prior) + math.log(first_lr))
    posterior_confirm = inv_logit(logit(prior) + math.log(first_lr) + math.log(confirm_lr))
    posterior_adversarial = inv_logit(logit(prior) + math.log(first_lr) + math.log(adversarial_lr))
    posterior_unspecified = inv_logit(logit(prior) + math.log(first_lr))
    lines.append("sequence posterior")
    lines.append(f"A_plus_only_unspecified_next {posterior_unspecified:.6f}")
    lines.append(f"A_plus_then_confirmatory_B {posterior_confirm:.6f}")
    lines.append(f"A_plus_then_adversarial_B {posterior_adversarial:.6f}")
    lines.append(f"spread_from_sequence_choice {max(posterior_confirm, posterior_adversarial)-min(posterior_confirm, posterior_adversarial):.6f}")
    lines.append(
        "NODE verdict: the same first observation does not define the update once the stream is "
        "interactive. The observation sequence/policy is part of the model."
    )
    return lines


def angle_diff(a: complex, b: complex) -> float:
    return abs(math.atan2(math.sin(math.atan2(a.imag, a.real) - math.atan2(b.imag, b.real)), math.cos(math.atan2(a.imag, a.real) - math.atan2(b.imag, b.real))))


def ema(x: np.ndarray, tau: float) -> np.ndarray:
    alpha = 1.0 - math.exp(-1.0 / tau)
    y = np.empty_like(x, dtype=float)
    y[0] = x[0]
    for i in range(1, len(x)):
        y[i] = (1.0 - alpha) * y[i - 1] + alpha * x[i]
    return y


def two_clock_series(sigma: float, window: tuple[float, float], samples: int, nprimes: int) -> tuple[np.ndarray, np.ndarray]:
    primes = first_primes(nprimes)
    tgrid = np.linspace(window[0], window[1], samples)
    errors = []
    tension = []
    for t in tgrid:
        s = complex(float(sigma), float(t))
        zp = dlog_zeta(s)
        fp = dlog_finite(s, primes)
        errors.append(angle_diff(zp, fp))
        tension.append(math.log1p(abs(zp)))
    return np.asarray(errors), ema(np.asarray(tension), tau=7.0)


def corr(a: np.ndarray, b: np.ndarray) -> float:
    aa = a - float(np.mean(a))
    bb = b - float(np.mean(b))
    den = float(np.linalg.norm(aa) * np.linalg.norm(bb))
    if den <= 1e-300:
        return 0.0
    return float(np.dot(aa, bb) / den)


def signed_metrics(errors: np.ndarray, tension: np.ndarray, q: float) -> dict[str, float]:
    gate = errors <= float(np.quantile(errors, q))
    gate_f = gate.astype(float)
    high = tension >= float(np.median(tension))
    uniform_corr = corr(gate_f, tension)
    gate_delta = (float(np.mean(tension[gate])) - float(np.mean(tension[~gate]))) / (float(np.std(tension)) + 1e-300)
    high_delta = float(np.mean(gate_f[high])) - float(np.mean(gate_f[~high]))
    lag_corrs = []
    for lag in range(-10, 11):
        if lag < 0:
            lag_corrs.append(corr(gate_f[-lag:], tension[:lag]))
        elif lag > 0:
            lag_corrs.append(corr(gate_f[:-lag], tension[lag:]))
        else:
            lag_corrs.append(uniform_corr)
    lag_corrs_arr = np.asarray(lag_corrs)
    return {
        "uniform_corr": uniform_corr,
        "gate_delta": gate_delta,
        "high_delta": high_delta,
        "lag_min": float(np.min(lag_corrs_arr)),
        "lag_max": float(np.max(lag_corrs_arr)),
        "lag_at_absmax": float(np.arange(-10, 11)[int(np.argmax(np.abs(lag_corrs_arr)))]),
        "corr_absmax": float(lag_corrs_arr[int(np.argmax(np.abs(lag_corrs_arr)))]),
    }


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Solomonoff/Bayesian sequence formulas do not apply unchanged to two-clock HGT data. "
        "The transfer keeps only the constraint: the statistic must specify its observation "
        "sequence."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 16: MINIMAL COUNTEREXAMPLE SEARCH")
    lines.append(
        "Counterexample target: find a reasonable observation sequence in which the critical "
        "two-clock sign is not anti-timed, or the right-side sign is not synchronized."
    )
    cases = [
        ("critical_low_s03", 0.30, (100.0, 170.0), "critical"),
        ("critical_low_s05", 0.50, (100.0, 170.0), "critical"),
        ("critical_low_s07", 0.70, (100.0, 170.0), "critical"),
        ("critical_high_s03", 0.30, (500.0, 570.0), "critical"),
        ("critical_high_s05", 0.50, (500.0, 570.0), "critical"),
        ("right_low_s12", 1.20, (100.0, 170.0), "right"),
        ("right_high_s12", 1.20, (500.0, 570.0), "right"),
    ]
    qs = [0.40, 0.50, 0.60]
    lines.append(
        "case region q uniform_corr gate_event_delta high_tension_gate_delta "
        "lag_min lag_max lag_absmax corr_absmax verdict"
    )
    critical_ok = 0
    critical_total = 0
    right_ok = 0
    right_total = 0
    for label, sigma, window, region in cases:
        errors, tension = two_clock_series(sigma, window, 720, 160)
        for q in qs:
            m = signed_metrics(errors, tension, q)
            if region == "critical":
                ok = m["uniform_corr"] < -0.12 and m["gate_delta"] < -0.20 and m["high_delta"] < -0.08
                critical_ok += int(ok)
                critical_total += 1
            else:
                ok = m["uniform_corr"] > 0.12 and m["gate_delta"] > 0.20 and m["high_delta"] > 0.08
                right_ok += int(ok)
                right_total += 1
            lines.append(
                f"{label:17s} {region:8s} {q:.2f} {m['uniform_corr']:+.4f} {m['gate_delta']:+.4f} "
                f"{m['high_delta']:+.4f} {m['lag_min']:+.4f} {m['lag_max']:+.4f} "
                f"{int(m['lag_at_absmax']):+03d} {m['corr_absmax']:+.4f} {int(ok)}"
            )
    lines.append("")
    lines.append(f"CRITICAL_SEQUENCE_SIGN_STABLE {critical_ok}/{critical_total}")
    lines.append(f"RIGHT_SEQUENCE_SIGN_STABLE {right_ok}/{right_total}")
    lines.append(
        "Interpretation: passing means the two-clock sign is not merely an artifact of sampling "
        "at uniform clock time; gate-event and high-tension-event sequences see the same sign. "
        "Failure would be a minimal observation-sequence counterexample."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: observation sequence -> two-clock layer")
    out.append(f"NODE: {NODE}")
    out.append(f"Standing-order target: {TARGET}")
    out.append(f"STEP 9 method: {METHOD}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
