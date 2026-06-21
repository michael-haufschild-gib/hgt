#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for major-loop/minor-loop hysteresis.

NODE constraint:
    A model fitted only to the major hysteresis loop can fail under partial
    cycling or reversal because hidden memory state is missing.

Step 8:
    Create three HT transfer attempts and select the lowest-Levenshtein one.

Step 9 method #10:
    Test extreme cases: zero memory width, left strip, right strip, finite Euler,
    amplitude-matched finite, random phase, and gain saturation.
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
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
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


def robust_norm(values: np.ndarray) -> np.ndarray:
    values = np.asarray(values, dtype=float)
    lo = float(np.quantile(values, 0.05))
    hi = float(np.quantile(values, 0.95))
    if hi <= lo + 1e-12:
        return np.zeros_like(values)
    return np.clip((values - lo) / (hi - lo), 0.0, 1.0)


def strip_features(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    amplitudes: list[float] = []
    defects: list[float] = []
    weights: list[float] = []
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
        amplitudes.append(math.log1p(abs(g + p)))
        defects.append(phase_defect(g, p))
        weights.append(math.log1p(abs(p)))
    center = 2.0 * robust_norm(np.asarray(amplitudes)) - 1.0
    memory = robust_norm(np.asarray(defects))
    raw_weights = 0.1 + robust_norm(np.asarray(weights))
    raw_weights /= float(np.sum(raw_weights))
    return center, memory, raw_weights


def run_hysterons(protocol: np.ndarray, alpha: np.ndarray, beta: np.ndarray, weights: np.ndarray, start: int = -1) -> np.ndarray:
    states = np.full(alpha.shape, start, dtype=int)
    out = []
    for h in protocol:
        states[h >= alpha] = 1
        states[h <= beta] = -1
        out.append(float(np.dot(weights, states)))
    return np.asarray(out)


def interpolate_branch(x: np.ndarray, h_branch: np.ndarray, y_branch: np.ndarray) -> np.ndarray:
    order = np.argsort(h_branch)
    return np.interp(x, h_branch[order], y_branch[order])


def major_loop_predict(protocol: np.ndarray, h_up: np.ndarray, y_up: np.ndarray, h_down: np.ndarray, y_down: np.ndarray) -> np.ndarray:
    pred = []
    prev = protocol[0]
    for h in protocol:
        if h >= prev:
            pred.append(float(interpolate_branch(np.array([h]), h_up, y_up)[0]))
        else:
            pred.append(float(interpolate_branch(np.array([h]), h_down, y_down)[0]))
        prev = h
    return np.asarray(pred)


def rmse(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.sqrt(np.mean((a - b) ** 2)))


def evaluate(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], gain: float, rng: np.random.Generator) -> dict[str, float]:
    center, memory, weights = strip_features(kind, sigma, window, samples, primes, rng)
    width = gain * memory
    alpha = np.clip(center + width, -1.25, 1.25)
    beta = np.clip(center - width, -1.25, 1.25)
    alpha = np.maximum(alpha, beta + 1e-6)

    up = np.linspace(-1.4, 1.4, 241)
    down = np.linspace(1.4, -1.4, 241)
    major = np.concatenate([up, down[1:]])
    major_true = run_hysterons(major, alpha, beta, weights)
    h_up = major[: len(up)]
    y_up = major_true[: len(up)]
    h_down = major[len(up) - 1 :]
    y_down = major_true[len(up) - 1 :]
    major_pred = major_loop_predict(major, h_up, y_up, h_down, y_down)
    minor = np.concatenate([
        np.linspace(-1.4, 0.95, 160),
        np.linspace(0.95, -0.25, 100),
        np.linspace(-0.25, 0.55, 80),
        np.linspace(0.55, -0.05, 60),
    ])
    minor_true = run_hysterons(minor, alpha, beta, weights)
    minor_pred = major_loop_predict(minor, h_up, y_up, h_down, y_down)
    return {
        "defect_med": float(np.median(memory)),
        "defect_pos": float(np.mean(memory > 0.0)),
        "width_med": float(np.median(width)),
        "width_q90": float(np.quantile(width, 0.90)),
        "major_rmse": rmse(major_true, major_pred),
        "minor_rmse": rmse(minor_true, minor_pred),
        "minor_max_abs": float(np.max(np.abs(minor_true - minor_pred))),
        "minor_area_true": float(np.trapz(minor_true, minor)),
        "minor_area_pred": float(np.trapz(minor_pred, minor)),
    }


def completed_dlog(kind: str, s: complex, primes: tuple[int, ...], rng: np.random.Generator) -> complex:
    """Completed xi-style log derivative, plus controls."""
    g = gamma_part(s)
    if kind == "true-completed":
        p = dlog_zeta(s)
    elif kind == "finite-completed":
        p = dlog_finite_euler(s, primes)
    elif kind == "ampmatched-finite":
        true_p = dlog_zeta(s)
        finite_p = dlog_finite_euler(s, primes)
        p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
    elif kind == "random-phase":
        true_p = dlog_zeta(s)
        theta = float(rng.uniform(-math.pi, math.pi))
        p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
    elif kind == "gamma-only":
        p = 0.0 + 0.0j
    else:
        raise ValueError(kind)
    return complex(1.0 / s + 1.0 / (s - 1.0) + g + p)


def fe_return_residuals(
    kind: str,
    protocol: np.ndarray,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> np.ndarray:
    residuals = []
    for sigma in protocol:
        vals = []
        for t in np.linspace(window[0], window[1], samples):
            s = complex(float(sigma), float(t))
            lhs = completed_dlog(kind, s, primes, rng)
            rhs = completed_dlog(kind, 1.0 - s, primes, rng)
            vals.append(math.log1p(abs(lhs + rhs)))
        residuals.append(float(np.median(vals)))
    return np.asarray(residuals)


def evaluate_fe_return(
    kind: str,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, float]:
    up = np.array([0.15, 0.35, 0.50, 0.65, 0.85])
    down = up[::-1]
    major = np.concatenate([up, down[1:]])
    minor = np.array([0.15, 0.78, 0.33, 0.68, 0.45])
    major_y = fe_return_residuals(kind, major, window, samples, primes, rng)
    minor_y = fe_return_residuals(kind, minor, window, samples, primes, rng)
    lookup = np.interp(minor, up, major_y[: len(up)])
    return {
        "major_med": float(np.median(major_y)),
        "major_q90": float(np.quantile(major_y, 0.90)),
        "minor_med": float(np.median(minor_y)),
        "minor_q90": float(np.quantile(minor_y, 0.90)),
        "minor_lookup_rmse": rmse(minor_y, lookup),
        "sigma_half_return": float(fe_return_residuals(kind, np.array([0.5]), window, samples, primes, rng)[0]),
    }


def run_functional_equation_return(args: argparse.Namespace) -> None:
    print("\nSTEP9 method #10: test extreme cases")
    print("selected branch: completed functional-equation return point under sigma reversal")
    print("residual = median_t log(1 + |L(s) + L(1-s)|) for completed log-derivative variants")
    print("kind window major_med major_q90 minor_med minor_q90 minor_lookup_rmse sigma_half_return")
    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(20260621)
    for window in [(14.0, 54.0), (100.0, 140.0), (500.0, 540.0)]:
        for kind in ["true-completed", "finite-completed", "ampmatched-finite", "random-phase", "gamma-only"]:
            out = evaluate_fe_return(kind, window, args.samples, primes, rng)
            print(
                f"{kind:18s} [{window[0]:.0f},{window[1]:.0f}] "
                f"{out['major_med']:.8f} {out['major_q90']:.8f} {out['minor_med']:.8f} "
                f"{out['minor_q90']:.8f} {out['minor_lookup_rmse']:.8f} "
                f"{out['sigma_half_return']:.8f}"
            )
    print(
        "\nInterpretation key: if the selected transfer only says the completed "
        "true object has near-zero FE mirror residual while finite/random/gamma "
        "controls do not, it reduces to the known functional equation and is "
        "not a new minor-loop memory invariant."
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    kernel = "models fitted only to the major loop fail under partial cycling or reversal"
    attempts = {
        "strip-minor-loop-reversal": "major loop fit fails under partial cycling or reversal in continuum strip phase memory",
        "functional-equation-return-point": "functional equation return point memory under sigma reversal",
        "prime-cutoff-coercivity": "finite prime cutoff coercivity during cutoff cycles",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:34s} distance={dist} normalized={dist / max(1, len(kernel)):.4f}")
    print(f"selected={selected}")
    if selected == "functional-equation-return-point":
        run_functional_equation_return(args)
        return
    if selected != "strip-minor-loop-reversal":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #10: test extreme cases")
    print("center=normalized log|Gamma_infty+P|, memory width=phase-defect component")
    print("kind sigma window gain defect_med defect_pos width_med width_q90 major_rmse minor_rmse minor_max_abs area_true area_pred")
    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(20260621)
    cases = [
        (0.3, (100.0, 170.0)),
        (0.3, (500.0, 570.0)),
        (0.5, (100.0, 170.0)),
        (0.7, (100.0, 170.0)),
        (1.2, (100.0, 170.0)),
    ]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    gains = [0.0, 0.25, 0.60, 1.00]
    for sigma, window in cases:
        for kind in kinds:
            for gain in gains:
                out = evaluate(kind, sigma, window, args.samples, primes, gain, rng)
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {gain:.2f} "
                    f"{out['defect_med']:.6f} {out['defect_pos']:.6f} {out['width_med']:.6f} "
                    f"{out['width_q90']:.6f} {out['major_rmse']:.8f} {out['minor_rmse']:.6f} "
                    f"{out['minor_max_abs']:.6f} {out['minor_area_true']:.6f} {out['minor_area_pred']:.6f}"
                )

    print(
        "\nInterpretation key: if minor-loop failure is zero at gain=0 and "
        "scales with the phase-defect width, then the transfer is a hysteresis "
        "wrapper around the existing left-strip phase-carrier observable."
    )


if __name__ == "__main__":
    main()
