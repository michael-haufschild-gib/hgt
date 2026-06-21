#!/usr/bin/env python3
"""THE-MACHINE run: similar alternatives compete more strongly.

NODE:
    In congested choice nodes, similar alternatives suppress one another more
    strongly than dissimilar alternatives.

STEP 9 method #21:
    Build a dependency chain. Here the chain is:
      (1) define similarity-weighted divisive normalization on NODE options;
      (2) validate similar distractors suppress more than dissimilar distractors;
      (3) transfer the exact chain to continuum HT traces using amplitude- and
          phase-similarity feature maps;
      (4) stress the boundary: if the result is just phase-carrier again, mark
          it reducing rather than post.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    target = np.array([1.0, 0.0])
    target_value = 1.0
    n = 1000
    tau = 0.35
    alpha = 1.8
    print("NODE simulation: similar alternatives suppress more strongly than dissimilar alternatives")
    print("case mean_similarity effective_value suppression")
    for name, center in [
        ("similar", np.array([0.85, 0.05])),
        ("dissimilar", np.array([0.0, 1.0])),
        ("mixed", np.array([0.45, 0.45])),
    ]:
        distractors = center + 0.12 * rng.normal(size=(n, 2))
        d2 = np.sum((distractors - target[None, :]) ** 2, axis=1)
        sim = np.exp(-d2 / (2.0 * tau * tau))
        denom = 1.0 + alpha * float(np.mean(sim))
        effective = target_value / denom
        print(f"{name:10s} {float(np.mean(sim)):.4f} {effective:.4f} {1.0 - effective:.4f}")


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
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


@dataclass(frozen=True)
class Trace:
    kind: str
    delta: np.ndarray
    amp_feature: np.ndarray
    phase_feature: np.ndarray


def make_trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> Trace:
    deltas = []
    amp = []
    phase = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        ag = abs(g)
        ap = abs(p)
        at = abs(g + p)
        d = phase_defect(g, p)
        cos = 0.0 if ag <= 1e-300 or ap <= 1e-300 else float((g * p.conjugate()).real / (ag * ap))
        deltas.append(d)
        amp.append([math.log1p(ag), math.log1p(ap), math.log1p(at), math.log((ap + 1e-300) / (ag + 1e-300))])
        phase.append([cos, d])
    return Trace(kind, np.asarray(deltas), np.asarray(amp), np.asarray(phase))


def standardize(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    mu = x.mean(axis=0, keepdims=True)
    sd = x.std(axis=0, keepdims=True)
    sd[sd < 1e-9] = 1.0
    return (x - mu) / sd


def suppression(target: Trace, distractor: Trace, feature: str, tau: float = 1.0, alpha: float = 2.0) -> dict[str, float]:
    xt = target.amp_feature if feature == "amp" else target.phase_feature
    xd = distractor.amp_feature if feature == "amp" else distractor.phase_feature
    x = standardize(np.vstack([xt, xd]))
    zt = x[: len(xt)]
    zd = x[len(xt) :]
    # Pair points at the same sampled height. This asks whether the distractor
    # occupies the same local option neighborhood as the target.
    d2 = np.sum((zt - zd) ** 2, axis=1)
    sim = np.exp(-d2 / (2.0 * tau * tau))
    raw_value = np.maximum(0.0, target.delta)
    effective = raw_value / (1.0 + alpha * sim)
    return {
        "raw_median": float(np.median(raw_value)),
        "sim_median": float(np.median(sim)),
        "effective_median": float(np.median(effective)),
        "suppression_median": float(np.median(raw_value - effective)),
    }


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "similar alternatives suppress target value by similarity weighted normalization"
    attempts = {
        "A_phase_similarity_suppression": "similar phase alternatives suppress phase carrier value by weighted normalization",
        "B_amplitude_similarity_suppression": "similar amplitude alternatives suppress magnitude value by weighted normalization",
        "C_sigma_cluster_suppression": "nearby sigma alternatives suppress target strip value by weighted normalization",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:34s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    rng = np.random.default_rng(7331)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: similarity-weighted suppression")
    print(f"samples={samples} finite_prime_count={prime_count}")
    print("sigma window target distractor feature raw_med sim_med effective_med suppression_med")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for window in windows:
            traces = {kind: make_trace(kind, sigma, window, samples, primes, rng) for kind in ["true", "finite", "random"]}
            for distractor in ["finite", "random"]:
                for feature in ["amp", "phase"]:
                    row = suppression(traces["true"], traces[distractor], feature)
                    print(
                        f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] true {distractor:6s} {feature:5s} "
                        f"{row['raw_median']:.4f} {row['sim_median']:.4f} "
                        f"{row['effective_median']:.4f} {row['suppression_median']:.4f}"
                    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
