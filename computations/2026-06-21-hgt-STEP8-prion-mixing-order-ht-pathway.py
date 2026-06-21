#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for prion-like mixing-order path dependence.

NODE constraint:
    Mixing order can change the assembly pathway and final material state even
    with identical final composition.

Step 8:
    Create three HT transfer attempts and select the lowest-Levenshtein one.

Step 9 method #11:
    Run experiments. Sweep strips, controls, and all mixing orders to ask
    whether order-memory survives as HT-specific continuum structure or merely
    restates an existing phase-defect statistic.
"""

from __future__ import annotations

import argparse
import itertools
import math

import mpmath as mp
import numpy as np


COMPONENTS = ("protein", "rna", "salt")


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


def carrier_values(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    values: list[complex] = []
    defects: list[float] = []
    amplitudes: list[float] = []
    true_cache: list[complex] = []
    finite_cache: list[complex] = []
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
        values.append(g + p)
        defects.append(phase_defect(g, p))
        amplitudes.append(math.log1p(abs(g + p)))
        true_cache.append(true_p)
        finite_cache.append(finite_p)

    angle = np.unwrap(np.angle(np.asarray(values, dtype=complex)))
    roughness = np.abs(np.gradient(angle))
    return robust_norm(np.asarray(defects)), robust_norm(np.asarray(amplitudes)), robust_norm(roughness)


def step_age(state: dict[str, np.ndarray], dt: float) -> None:
    p = state["protein_free"]
    r = state["rna_free"]
    s = state["salt"]
    liquid = state["liquid"]
    gel = state["gel"]
    fiber = state["fiber"]

    liquid_form = np.minimum(dt * (0.62 * p * r / (1.0 + 0.7 * s)), np.minimum(p, r))
    self_seed = np.minimum(dt * (0.18 * p * p / (1.0 + 5.0 * r)), np.maximum(0.0, p - liquid_form))
    gelation = np.minimum(dt * (0.035 + 0.20 * s + 0.06 * p) * liquid, liquid + liquid_form)
    fiber_template = np.minimum(
        dt * (0.24 * fiber * p + 0.05 * gel * p),
        np.maximum(0.0, p - liquid_form - self_seed + gel),
    )
    salt_dissolve = np.minimum(
        dt * (0.035 * s * (liquid + liquid_form) / (1.0 + r)),
        np.maximum(0.0, liquid + liquid_form - gelation),
    )

    state["protein_free"] = np.maximum(0.0, p - liquid_form - self_seed - np.maximum(0.0, fiber_template - gel))
    state["rna_free"] = np.maximum(0.0, r - 0.72 * liquid_form)
    state["liquid"] = np.maximum(0.0, liquid + liquid_form - gelation - salt_dissolve)
    state["gel"] = np.maximum(0.0, gel + gelation - np.minimum(gel, fiber_template))
    state["fiber"] = np.maximum(0.0, fiber + self_seed + fiber_template)
    state["soluble"] = np.maximum(0.0, state["soluble"] + salt_dissolve)


def run_order(components: dict[str, np.ndarray], order: tuple[str, ...], age_steps: int = 8, dt: float = 0.045) -> np.ndarray:
    n = len(next(iter(components.values())))
    state = {key: np.zeros(n) for key in ["protein_free", "rna_free", "salt", "liquid", "gel", "fiber", "soluble"]}
    for component in order:
        if component == "protein":
            state["protein_free"] += components["protein"]
        elif component == "rna":
            state["rna_free"] += components["rna"]
        elif component == "salt":
            state["salt"] += components["salt"]
        else:
            raise ValueError(component)
        for _ in range(age_steps):
            step_age(state, dt)
    for _ in range(4 * age_steps):
        step_age(state, dt)
    return np.array([
        float(np.median(state["liquid"])),
        float(np.median(state["gel"])),
        float(np.median(state["fiber"])),
        float(np.median(state["soluble"])),
    ])


def order_summary(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    defect, amplitude, roughness = carrier_values(kind, sigma, window, samples, primes, rng)
    components = {
        "protein": defect,
        "rna": amplitude,
        "salt": roughness,
    }
    vectors = []
    labels = []
    for order in itertools.permutations(COMPONENTS):
        vec = run_order(components, order)
        vectors.append(vec)
        labels.append("-".join(order))
    arr = np.asarray(vectors)
    pairwise = [
        float(np.linalg.norm(arr[i] - arr[j], ord=1))
        for i in range(len(arr))
        for j in range(i + 1, len(arr))
    ]
    best = int(np.argmax(arr[:, 2] + arr[:, 1]))
    worst = int(np.argmin(arr[:, 2] + arr[:, 1]))
    return {
        "defect_median": float(np.median(defect)),
        "defect_positive_fraction": float(np.mean(defect > 0.0)),
        "max_order_spread": max(pairwise) if pairwise else 0.0,
        "fiber_range": (float(np.min(arr[:, 2])), float(np.max(arr[:, 2]))),
        "gel_range": (float(np.min(arr[:, 1])), float(np.max(arr[:, 1]))),
        "liquid_range": (float(np.min(arr[:, 0])), float(np.max(arr[:, 0]))),
        "best_order": labels[best],
        "worst_order": labels[worst],
        "best_vec": arr[best],
        "worst_vec": arr[worst],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    kernel = "order of mixing components changes assembly pathway and final material state"
    attempts = {
        "strip-pathway-order": "order of mixing components changes assembly pathway and final material state in continuum strip observables",
        "prime-block-aging": "finite prime cutoff blocks nucleate aged assemblies before archimedean completion",
        "zero-shadow-seeding": "zero shadow cavities seed irreversible fibers under sampling and blur",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:24s} distance={dist} normalized={dist / max(1, len(kernel)):.4f}")
    print(f"selected={selected}")
    if selected != "strip-pathway-order":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #11: run experiments")
    print("component map: protein=phase_defect(Gamma_infty,P), rna=log|Gamma_infty+P|, salt=local phase roughness")
    print("kind sigma window defect_med defect_pos max_order_spread fiber_min fiber_max gel_min gel_max liquid_min liquid_max best_order worst_order")

    primes = first_primes(args.prime_count)
    cases = [
        (0.3, (100.0, 170.0)),
        (0.3, (500.0, 570.0)),
        (0.5, (100.0, 170.0)),
        (0.7, (100.0, 170.0)),
        (1.2, (100.0, 170.0)),
    ]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            summary = order_summary(kind, sigma, window, args.samples, primes, seed=20260621 + 100 * case_index + kind_index)
            fiber_min, fiber_max = summary["fiber_range"]
            gel_min, gel_max = summary["gel_range"]
            liquid_min, liquid_max = summary["liquid_range"]
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{summary['defect_median']:.6f} {summary['defect_positive_fraction']:.6f} "
                f"{summary['max_order_spread']:.6f} {fiber_min:.6f} {fiber_max:.6f} "
                f"{gel_min:.6f} {gel_max:.6f} {liquid_min:.6f} {liquid_max:.6f} "
                f"{summary['best_order']} {summary['worst_order']}"
            )
            if kind == "true" and sigma == 0.3:
                print(
                    "  true_best_vec="
                    + ",".join(f"{x:.6f}" for x in summary["best_vec"])
                    + " true_worst_vec="
                    + ",".join(f"{x:.6f}" for x in summary["worst_vec"])
                )

    print(
        "\nInterpretation key: a non-reducing result would need order-memory not "
        "explained by the already-known left-strip phase-carrier defect. If "
        "max_order_spread tracks defect_median and collapses with phase controls "
        "or on sigma=1.2, the transfer reduces to known phase-defect content."
    )


if __name__ == "__main__":
    main()
