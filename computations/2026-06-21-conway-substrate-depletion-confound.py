#!/usr/bin/env python3
"""THE-MACHINE run: substrate depletion masquerading as inhibition."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def fit_exponential_inhibition(times: np.ndarray, product: np.ndarray) -> tuple[float, float, float]:
    """Fit product(t) = a * (1 - exp(-k t)) / k, returning k, a, normalized rmse."""
    y = product - product[0]
    y_range = float(np.max(y) - np.min(y))
    if y_range <= 1e-12:
        return 0.0, 0.0, 0.0
    best = (float("inf"), 0.0, 0.0)
    for k in np.concatenate(([0.0], np.geomspace(1e-4, 0.24, 170))):
        if k < 1e-12:
            basis = times - times[0]
        else:
            basis = (1.0 - np.exp(-k * (times - times[0]))) / k
        denom = float(np.dot(basis, basis))
        if denom <= 1e-18:
            continue
        a = max(0.0, float(np.dot(y, basis) / denom))
        err = float(np.sqrt(np.mean((a * basis - y) ** 2)) / y_range)
        if err < best[0]:
            best = (err, float(k), a)
    return best[1], best[2], best[0]


def node_dense_network(
    *,
    reporter_s0: float,
    competitor_s0: float,
    density: float,
    t_end: float,
    dt: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """No-inhibitor protease network with finite reporter and competitor substrate pools."""
    times = np.arange(0.0, t_end + 0.5 * dt, dt)
    reporter = reporter_s0
    competitors = np.full(6, competitor_s0 / 6.0)
    product = 0.0
    products = []
    rates = []
    enzymes = np.asarray([0.42, 0.33, 0.28, 0.19])
    km_r = np.asarray([0.32, 0.55, 0.78, 1.10])
    kcat_r = np.asarray([1.10, 0.86, 0.64, 0.44])
    km_c = np.asarray([0.22, 0.35, 0.52, 0.80])
    kcat_c = np.asarray([0.84, 0.72, 0.58, 0.39])
    weights = np.asarray(
        [
            [1.0, 0.8, 0.6, 0.4, 0.2, 0.1],
            [0.9, 1.0, 0.7, 0.3, 0.1, 0.2],
            [0.3, 0.7, 1.0, 0.8, 0.4, 0.1],
            [0.1, 0.2, 0.5, 0.9, 1.0, 0.7],
        ]
    )
    weights = (1.0 - density) * np.eye(4, 6) + density * weights
    for _ in times:
        comp_load = weights @ competitors
        reporter_fluxes = enzymes * kcat_r * reporter / (km_r + reporter + comp_load + 1e-12)
        comp_fluxes = []
        for j in range(len(competitors)):
            denom = km_c + reporter + comp_load + 1e-12
            comp_fluxes.append(float(np.sum(enzymes * kcat_c * weights[:, j] * competitors[j] / denom)))
        reporter_rate = float(np.sum(reporter_fluxes))
        comp_rates = np.asarray(comp_fluxes)
        step_r = min(reporter, reporter_rate * dt)
        reporter -= step_r
        if reporter_rate > 1e-12:
            product += step_r
        for j, r in enumerate(comp_rates):
            competitors[j] = max(0.0, competitors[j] - r * dt)
        products.append(product)
        rates.append(reporter_rate)
    return times, np.asarray(products), np.asarray(rates)


def node_experiment() -> None:
    print("NODE simulation: no-inhibitor substrate depletion fitted as apparent time-dependent inhibition")
    print("case reporter_s0 competitor_s0 density k_app amp nrmse early_late_rate masquerade")
    cases = [
        ("early_excess_control", 25.0, 4.0, 0.35, 8.0),
        ("finite_reporter", 4.0, 2.0, 0.45, 18.0),
        ("dense_competition", 4.0, 12.0, 0.85, 18.0),
        ("near_exhaustion", 1.6, 10.0, 0.85, 18.0),
    ]
    for name, reporter_s0, competitor_s0, density, t_end in cases:
        times, product, rates = node_dense_network(
            reporter_s0=reporter_s0,
            competitor_s0=competitor_s0,
            density=density,
            t_end=t_end,
            dt=0.025,
        )
        k, amp, nrmse = fit_exponential_inhibition(times, product)
        early = float(np.mean(rates[: max(4, len(rates) // 8)]))
        late = float(np.mean(rates[-max(4, len(rates) // 8) :]))
        ratio = early / max(late, 1e-12)
        masquerade = int(k > 0.035 and nrmse < 0.055 and ratio > 1.35)
        print(
            f"{name:20s} {reporter_s0:7.2f} {competitor_s0:7.2f} {density:5.2f} "
            f"{k:7.4f} {amp:7.4f} {nrmse:7.4f} {ratio:9.3f} {masquerade}"
        )


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def run_levenshtein() -> None:
    node_sig = "substrate depletion masquerades as protease inhibition in dense reaction networks"
    candidates = [
        "phase defect depletion masquerades as analytic damping in dense continuum traces",
        "zero shadow exhaustion masquerades as obstruction inhibition in critical strip traces",
        "cancellation budget depletion masquerades as differential inhibition in analytic networks",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for i, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{i} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, i, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")


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


def ht_rate_trace(
    kind: str,
    sigma: float,
    start: float,
    end: float,
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
    mode: str,
) -> tuple[np.ndarray, np.ndarray]:
    times = np.linspace(start, end, samples)
    defects = []
    amplitudes = []
    for t in times:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        else:
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        defects.append(phase_defect(g, p))
        amplitudes.append(math.log(abs(g) + abs(p) + 1e-300))
    d = np.asarray(defects)
    a = np.asarray(amplitudes)
    if mode == "phase":
        threshold = float(np.quantile(d, 0.62))
        rates = np.maximum(d - threshold, 0.0)
    elif mode == "amplitude":
        threshold = float(np.quantile(a, 0.62))
        rates = np.maximum(a - threshold, 0.0)
    elif mode == "shuffled":
        threshold = float(np.quantile(d, 0.62))
        rates = np.maximum(d - threshold, 0.0)
        rng.shuffle(rates)
    else:
        raise ValueError(mode)
    return times - times[0], rates


def product_from_rates(times: np.ndarray, rates: np.ndarray) -> np.ndarray:
    if len(times) < 2:
        return np.zeros_like(times)
    dt = float(np.mean(np.diff(times)))
    return np.cumsum(rates) * dt


def summarize_ht_trace(times: np.ndarray, rates: np.ndarray) -> tuple[float, float, float, float]:
    product = product_from_rates(times, rates)
    k, amp, nrmse = fit_exponential_inhibition(times, product)
    n = len(rates)
    early = float(np.mean(rates[: max(4, n // 5)]))
    late = float(np.mean(rates[-max(4, n // 5) :]))
    ratio = early / max(late, 1e-12)
    active = float(np.mean(rates > 1e-12))
    return k, nrmse, ratio, active


def ht_experiment(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: phase-defect depletion masquerading as damping")
    print(f"samples={samples} prime_count={prime_count}")
    print(
        "kind sigma window phase_k phase_nrmse phase_early_late phase_active "
        "shuffle_k shuffle_nrmse amp_k amp_nrmse breaks_false"
    )
    windows = [(100.0, 190.0), (500.0, 590.0)]
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            for wi, (start, end) in enumerate(windows, 1):
                seed = 902000 + int(100 * sigma) + 1000 * wi + {"true": 1, "finite": 2, "random": 3}[kind]
                rng = np.random.default_rng(seed)
                times, rates = ht_rate_trace(kind, sigma, start, end, samples, primes, rng, "phase")
                phase_k, phase_nrmse, ratio, active = summarize_ht_trace(times, rates)
                rng = np.random.default_rng(seed + 77)
                _, shuf_rates = ht_rate_trace(kind, sigma, start, end, samples, primes, rng, "shuffled")
                shuf_k, shuf_nrmse, _, _ = summarize_ht_trace(times, shuf_rates)
                rng = np.random.default_rng(seed + 131)
                _, amp_rates = ht_rate_trace(kind, sigma, start, end, samples, primes, rng, "amplitude")
                amp_k, amp_nrmse, _, _ = summarize_ht_trace(times, amp_rates)
                breaks_false = int(
                    kind == "true"
                    and sigma < 0.9
                    and phase_k > 0.012
                    and phase_nrmse < 0.13
                    and ratio > 1.55
                    and shuf_k < 0.55 * phase_k
                    and amp_k < 0.70 * phase_k
                )
                print(
                    f"{kind:6s} {sigma:.1f} {wi:d} {phase_k:8.5f} {phase_nrmse:8.4f} "
                    f"{ratio:9.3f} {active:8.3f} {shuf_k:8.5f} {shuf_nrmse:8.4f} "
                    f"{amp_k:8.5f} {amp_nrmse:8.4f} {breaks_false:d}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_experiment()
    run_levenshtein()
    ht_experiment(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
