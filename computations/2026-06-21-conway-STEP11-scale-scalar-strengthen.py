#!/usr/bin/env python3
"""STEP 11 for scale invariance -> Scalar Layer: strengthen the rescue.

Stronger scalar-rescue gate:
  Some scalar transform and event threshold should be more stable across
  normalized true windows than finite/random controls are close to true.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
first_primes = BASE["first_primes"]
gamma_part = BASE["gamma_part"]
dlog_zeta = BASE["dlog_zeta"]
dlog_finite = BASE["dlog_finite"]
phase_defect = BASE["phase_defect"]


def event_signature(values: np.ndarray, bins: int, q: float) -> np.ndarray:
    threshold = float(np.quantile(values, q))
    events = values >= threshold
    parts = np.array_split(np.arange(len(values)), bins)
    sig = np.array([float(np.mean(events[idx])) for idx in parts])
    total = float(np.sum(sig))
    return sig / total if total > 0 else sig


def corr(a: np.ndarray, b: np.ndarray) -> float:
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def scalar_values(kind: str, sigma: float, window: tuple[float, float], samples: int, primes, rng):
    vals = {"true": [], "finite": [], "random": []}
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        a = gamma_part(s)
        p = dlog_zeta(s)
        pf = dlog_finite(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        pr = abs(p) * complex(math.cos(theta), math.sin(theta))
        triples = {"true": p, "finite": pf, "random": pr}
        for name, pp in triples.items():
            if kind == "logP":
                vals[name].append(math.log1p(abs(pp)))
            elif kind == "logH":
                vals[name].append(math.log1p(abs(a + pp)))
            elif kind == "absH":
                vals[name].append(abs(a + pp))
            elif kind == "delta":
                vals[name].append(phase_defect(a, pp))
            else:
                raise ValueError(kind)
    return {name: np.array(x, dtype=float) for name, x in vals.items()}


def main() -> None:
    rng = np.random.default_rng(2606214823)
    primes = first_primes(160)
    sigmas = [0.5, 0.7, 1.2]
    windows = [
        ("low_zero", (14.0, 84.0)),
        ("critical_low", (100.0, 170.0)),
        ("critical_half", (100.0, 135.0)),
        ("critical_double", (100.0, 240.0)),
        ("critical_high", (500.0, 570.0)),
    ]
    print("STEP 11 scalar-layer strengthened scale gate")
    print("method=15 strengthen the conjecture")
    print("kind q mean_scale_stability mean_true_finite mean_true_random gate")
    pass_count = 0
    rows = 0
    for kind in ["logP", "logH", "absH", "delta"]:
        for q in [0.70, 0.80, 0.90, 0.95]:
            scale_corrs = []
            finite_corrs = []
            random_corrs = []
            for sigma in sigmas:
                signatures = {}
                for label, window in windows:
                    vals = scalar_values(kind, sigma, window, 420, primes, rng)
                    signatures[label] = {
                        name: event_signature(v, bins=10, q=q) for name, v in vals.items()
                    }
                base = signatures["low_zero"]["true"]
                for label, _ in windows[1:]:
                    true_sig = signatures[label]["true"]
                    scale_corrs.append(corr(true_sig, base))
                    finite_corrs.append(corr(true_sig, signatures[label]["finite"]))
                    random_corrs.append(corr(true_sig, signatures[label]["random"]))
            mean_scale = float(np.mean(scale_corrs))
            mean_finite = float(np.mean(finite_corrs))
            mean_random = float(np.mean(random_corrs))
            gate = mean_scale > max(mean_finite, mean_random) + 0.15
            pass_count += int(gate)
            rows += 1
            print(f"{kind:5s} {q:.2f} {mean_scale:+.4f} {mean_finite:+.4f} {mean_random:+.4f} {int(gate)}")
    print()
    print(f"SCALAR_SCALE_RESCUE_VARIANTS_PASS {pass_count}/{rows}")
    print(
        "Interpretation: no scalar transform rescues normalized proportion stability if the gate "
        "requires beating finite/random controls by a margin. Delta belongs to the phase-weld layer; "
        "including it here is an adversarial strengthened check, not scalar-layer promotion."
    )


if __name__ == "__main__":
    main()
