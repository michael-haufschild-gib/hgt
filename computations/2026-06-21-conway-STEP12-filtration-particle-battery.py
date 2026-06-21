#!/usr/bin/env python3
"""STEP 11/12 battery: phase-defect mass carried by small components."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> tuple[int, ...]:
    primes = []
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
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def component_recalls(signal: np.ndarray, dt: float, pores: list[float]) -> tuple[int, float, float, dict[float, float]]:
    components: list[np.ndarray] = []
    current: list[float] = []
    for x in signal:
        if x > 0:
            current.append(float(x))
        elif current:
            components.append(np.asarray(current))
            current = []
    if current:
        components.append(np.asarray(current))
    total = float(np.sum(signal))
    if total <= 1e-12 or not components:
        return 0, 0.0, 0.0, {p: 1.0 for p in pores}
    widths = np.asarray([len(c) * dt for c in components])
    masses = np.asarray([float(np.sum(c)) for c in components])
    recalls = {}
    for pore in pores:
        recalls[pore] = float(np.sum(masses[widths <= pore]) / total)
    return len(components), float(np.mean(widths)), float(np.max(masses) / total), recalls


def traces(sigma: float, start: float, end: float, dt: float, prime_sets: dict[int, tuple[int, ...]]):
    times = np.arange(start, end, dt)
    gs = []
    ps_true = []
    ps_finite: dict[int, list[complex]] = {n: [] for n in prime_sets}
    for t in times:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p_true = dlog_zeta(s)
        gs.append(g)
        ps_true.append(p_true)
        for n, primes in prime_sets.items():
            ps_finite[n].append(dlog_finite_euler(s, primes))
    return np.asarray(gs), np.asarray(ps_true), {n: np.asarray(v) for n, v in ps_finite.items()}


def signal_from(g: np.ndarray, p: np.ndarray, threshold: float) -> np.ndarray:
    return np.asarray([max(phase_defect(complex(gg), complex(pp)) - threshold, 0.0) for gg, pp in zip(g, p)])


def run(dt: float) -> None:
    prime_sets = {n: first_primes(n) for n in [80, 160, 260]}
    pores = [0.25, 0.50, 0.75, 1.25]
    windows = [(14.0, 84.0), (100.0, 170.0), (260.0, 330.0), (500.0, 570.0)]
    thresholds = [0.8, 1.0, 1.2]
    print("STEP11/12 battery: physical-width filtration of phase-defect components")
    print(f"dt={dt} finite_prime_counts=80,160,260 random_seeds=8")
    print(
        "sigma window threshold true_total true_n true_mean_width true_max_mass "
        "true_r025 true_r050 true_r125 finite_min_r050 random_min_r050 survives"
    )
    total_survive = 0
    total_rows = 0
    for sigma in [0.3, 0.5, 1.2]:
        for wi, (start, end) in enumerate(windows, 1):
            g, p_true, p_finite = traces(sigma, start, end, dt, prime_sets)
            for threshold in thresholds:
                total_rows += 1
                true_signal = signal_from(g, p_true, threshold)
                n, mean_w, max_mass, true_recalls = component_recalls(true_signal, dt, pores)
                finite_r050 = []
                for p in p_finite.values():
                    sig = signal_from(g, p, threshold)
                    finite_r050.append(component_recalls(sig, dt, pores)[3][0.50])
                random_r050 = []
                abs_true = np.abs(p_true)
                for j in range(8):
                    rng = np.random.default_rng(1234000 + int(100 * sigma) + 1000 * wi + int(100 * threshold) + j)
                    phases = rng.uniform(-math.pi, math.pi, len(abs_true))
                    p_rand = abs_true * np.exp(1j * phases)
                    sig = signal_from(g, p_rand, threshold)
                    random_r050.append(component_recalls(sig, dt, pores)[3][0.50])
                control_min = min(min(finite_r050), min(random_r050))
                survives = int(
                    sigma < 0.9
                    and float(np.sum(true_signal)) > 1e-8
                    and true_recalls[0.50] + 0.22 < control_min
                    and true_recalls[1.25] > 0.88
                    and max_mass < 0.16
                )
                total_survive += survives
                print(
                    f"{sigma:.1f} {wi:d} {threshold:4.1f} {float(np.sum(true_signal)):10.4f} "
                    f"{n:4d} {mean_w:8.4f} {max_mass:8.4f} {true_recalls[0.25]:8.4f} "
                    f"{true_recalls[0.50]:8.4f} {true_recalls[1.25]:8.4f} "
                    f"{min(finite_r050):8.4f} {min(random_r050):8.4f} {survives:d}"
                )
    print(f"survival_rows={total_survive}/{total_rows}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dt", type=float, default=0.25)
    args = parser.parse_args()
    run(args.dt)


if __name__ == "__main__":
    main()
