#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for battery temperature/SOC hysteresis.

NODE constraint:
    Temperature changes both voltage-SOC calibration and hysteresis behavior.

Step 8:
    Create three wildly different HT transfer attempts and select the
    lowest-Levenshtein one.

Step 9 method #23:
    Classify boundary cases for a reference-lane calibration: learn a
    voltage-like amplitude+history readout at sigma=0.5, then test other sigma
    lanes and controls.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = cur
    return prev[-1]


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def robust_norm(values: np.ndarray, lo: float | None = None, hi: float | None = None) -> tuple[np.ndarray, float, float]:
    values = np.asarray(values, dtype=float)
    if lo is None:
        lo = float(np.quantile(values, 0.05))
    if hi is None:
        hi = float(np.quantile(values, 0.95))
    if hi <= lo + 1e-12:
        return np.zeros_like(values), lo, hi
    return np.clip((values - lo) / (hi - lo), 0.0, 1.0), lo, hi


def lane(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    amp: list[float] = []
    defect: list[float] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite_euler(s, primes)
        if kind == "true":
            p = true_p
        elif kind == "finite":
            p = finite_p
        elif kind == "ampmatched-finite":
            p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
        elif kind == "random-phase":
            theta = float(rng.uniform(-math.pi, math.pi))
            p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        elif kind == "gamma-only":
            p = 0.0 + 0.0j
        else:
            raise ValueError(kind)
        amp.append(math.log1p(abs(g + p)))
        defect.append(phase_defect(g, p))
    return {"amp": np.asarray(amp), "defect": np.asarray(defect)}


def history_state(n: int, tau: float) -> np.ndarray:
    protocol = np.concatenate([np.arange(n), np.arange(n - 1, -1, -1)])
    target = np.concatenate([np.ones(n), -np.ones(n)])
    h = np.zeros(len(protocol))
    for k in range(1, len(protocol)):
        h[k] = h[k - 1] + (target[k - 1] - h[k - 1]) / tau
    return h


def make_trace(data: dict[str, np.ndarray], amp_lo: float | None, amp_hi: float | None, gain: float, tau: float) -> tuple[np.ndarray, np.ndarray, float, float]:
    n = len(data["amp"])
    idx = np.concatenate([np.arange(n), np.arange(n - 1, -1, -1)])
    amp_norm, lo, hi = robust_norm(data["amp"], amp_lo, amp_hi)
    h = history_state(n, tau)
    voltage = amp_norm[idx] + gain * h
    hidden = data["defect"][idx]
    return voltage, hidden, lo, hi


def estimate_hidden(voltage_ref: np.ndarray, hidden_ref: np.ndarray, voltage: np.ndarray) -> np.ndarray:
    order = np.argsort(voltage_ref)
    return np.interp(voltage, voltage_ref[order], hidden_ref[order])


def evaluate(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    seed: int,
) -> dict[str, float]:
    rng_ref = np.random.default_rng(seed)
    rng_target = np.random.default_rng(seed + 1)
    ref = lane(kind, 0.5, window, samples, primes, rng_ref)
    target = lane(kind, sigma, window, samples, primes, rng_target)
    ref_gain = 0.03 + 0.45 * float(np.median(ref["defect"]))
    target_gain = 0.03 + 0.45 * float(np.median(target["defect"]))
    ref_tau = 10.0 + 28.0 * float(np.median(ref["defect"] > 0.0))
    target_tau = 10.0 + 28.0 * float(np.median(target["defect"] > 0.0))
    v_ref, h_ref, amp_lo, amp_hi = make_trace(ref, None, None, ref_gain, ref_tau)

    modes: dict[str, float] = {}
    for mode in ["full", "ocv_only", "hysteresis_only"]:
        if mode == "full":
            v, h, _, _ = make_trace(target, amp_lo, amp_hi, target_gain, target_tau)
        elif mode == "ocv_only":
            v, h, _, _ = make_trace(target, amp_lo, amp_hi, ref_gain, ref_tau)
        else:
            ref_amp_shape = {"amp": ref["amp"], "defect": target["defect"]}
            v, h, _, _ = make_trace(ref_amp_shape, amp_lo, amp_hi, target_gain, target_tau)
        pred = estimate_hidden(v_ref, h_ref, v)
        modes[mode] = float(np.median(np.abs(pred - h)))
    return {
        "defect_med": float(np.median(target["defect"])),
        "defect_pos": float(np.mean(target["defect"] > 0.0)),
        "ref_gain": ref_gain,
        "target_gain": target_gain,
        **modes,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=140)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()

    kernel = "temperature changes alter both hysteresis behavior and OCV SOC calibration"
    attempts = {
        "strip-temperature-calibration": "temperature changes alter both phase hysteresis behavior and strip OCV calibration",
        "prime-thermal-cutoff": "finite prime cutoff temperature changes Euler product calibration",
        "zero-thermal-relaxation": "zero neighborhood relaxation changes hysteresis after load removal",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:31s} distance={dist} normalized={dist / max(1, len(kernel)):.4f}")
    print(f"selected={selected}")
    if selected != "strip-temperature-calibration":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #23: classify boundary cases")
    print("reference calibration lane: sigma=0.5; hidden SOC analogue=phase defect; voltage analogue=amplitude+history")
    print("signal threshold: full_error >= 0.05")
    print("kind sigma window defect_med defect_pos ref_gain target_gain full_error ocv_only_error hysteresis_only_error signal")
    primes = first_primes(args.prime_count)
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.7, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            out = evaluate(kind, sigma, window, args.samples, primes, seed=20260621 + 97 * case_index + kind_index)
            signal = int(out["full"] >= 0.05)
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{out['defect_med']:.6f} {out['defect_pos']:.6f} "
                f"{out['ref_gain']:.6f} {out['target_gain']:.6f} "
                f"{out['full']:.6f} {out['ocv_only']:.6f} {out['hysteresis_only']:.6f} {signal:d}"
            )

    print(
        "\nInterpretation key: if calibration failure is large only where phase "
        "defect is already large, or if random/amplitude controls also fail, the "
        "temperature metaphor reduces to known phase-defect/calibration artifacts."
    )


if __name__ == "__main__":
    main()
