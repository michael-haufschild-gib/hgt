#!/usr/bin/env python3
"""THE-MACHINE run: population immunity changes favored directions."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    directions = np.array([[1.0, 0.0], [0.5, 0.866], [-0.5, 0.866], [-1.0, 0.0], [0.0, -1.0]])
    intrinsic = np.array([1.0, 0.0])
    memory = np.zeros(2)
    beta = 2.8
    decay = 0.90
    sigma = 0.65
    chosen = []
    no_memory_choice = int(np.argmax(directions @ intrinsic))
    for _ in range(120):
        immune_penalty = np.exp(-np.sum((directions - memory[None, :]) ** 2, axis=1) / (2 * sigma * sigma))
        score = directions @ intrinsic - beta * immune_penalty + 0.04 * rng.normal(size=len(directions))
        j = int(np.argmax(score))
        chosen.append(j)
        memory = decay * memory + (1.0 - decay) * directions[j]
    counts = np.bincount(np.asarray(chosen), minlength=len(directions)) / len(chosen)
    angle = math.degrees(math.acos(np.clip(float(directions[np.argmax(counts)] @ intrinsic), -1.0, 1.0)))
    print("NODE simulation: population immunity rotates favored antigenic direction")
    print(f"no_memory_choice={no_memory_choice} no_memory_angle=0.0")
    print("direction_index fraction")
    for i, frac in enumerate(counts):
        print(f"{i} {frac:.3f}")
    print(f"dominant_with_memory={int(np.argmax(counts))} rotation_angle_deg={angle:.2f}")


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


def component(kind: str, s: complex, primes: tuple[int, ...], rng: np.random.Generator) -> complex:
    if kind == "true":
        return dlog_zeta(s)
    if kind == "finite":
        return dlog_finite_euler(s, primes)
    if kind == "random":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        return abs(base) * complex(math.cos(theta), math.sin(theta))
    raise ValueError(kind)


def feedback_path(kind: str, window: tuple[float, float], samples: int, primes: tuple[int, ...], beta: float, rng: np.random.Generator):
    sigmas = np.array([0.25, 0.35, 0.50, 0.65, 0.80])
    memory = np.zeros_like(sigmas)
    decay = 0.94
    choices = []
    raw_choices = []
    rotations = []
    for t in np.linspace(window[0], window[1], samples):
        raw = []
        for sigma in sigmas:
            s = complex(float(sigma), float(t))
            raw.append(max(0.0, phase_defect(gamma_part(s), component(kind, s, primes, rng))))
        raw_arr = np.asarray(raw)
        raw_choice = int(np.argmax(raw_arr))
        score = raw_arr - beta * memory
        choice = int(np.argmax(score))
        choices.append(choice)
        raw_choices.append(raw_choice)
        rotations.append(abs(sigmas[choice] - sigmas[raw_choice]))
        memory = decay * memory
        memory[choice] += (1.0 - decay) * (1.0 + raw_arr[choice])
    choices_arr = np.asarray(choices)
    raw_arr = np.asarray(raw_choices)
    return {
        "raw_left_frac": float(np.mean(raw_arr <= 1)),
        "feedback_left_frac": float(np.mean(choices_arr <= 1)),
        "choice_entropy": float(-np.sum([p * math.log(p + 1e-12) for p in np.bincount(choices_arr, minlength=len(sigmas)) / len(choices_arr)])),
        "raw_entropy": float(-np.sum([p * math.log(p + 1e-12) for p in np.bincount(raw_arr, minlength=len(sigmas)) / len(raw_arr)])),
        "mean_rotation": float(np.mean(rotations)),
        "switch_rate": float(np.mean(choices_arr[1:] != choices_arr[:-1])),
    }


def ht_run(samples: int, prime_count: int) -> None:
    kernel = "population immunity feedback changes favored antigenic direction"
    attempts = {
        "A_phase_memory_direction": "phase memory feedback changes favored sigma direction",
        "B_amplitude_memory_direction": "amplitude memory feedback changes favored magnitude direction",
        "C_zero_memory_direction": "zero proximity memory feedback changes favored valley direction",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:28s} distance={dist}")
    print(f"selected={selected}")

    primes = first_primes(prime_count)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: history-conditioned phase-selection direction")
    print(f"samples={samples} finite_prime_count={prime_count}")
    print("kind window raw_left feedback_left raw_entropy choice_entropy mean_rotation switch_rate")
    for kind in ["true", "finite", "random"]:
        for window in windows:
            rng = np.random.default_rng(9900 + int(window[0]) + {"true": 1, "finite": 2, "random": 3}[kind])
            row = feedback_path(kind, window, samples, primes, beta=0.55, rng=rng)
            print(
                f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] "
                f"{row['raw_left_frac']:.3f} {row['feedback_left_frac']:.3f} "
                f"{row['raw_entropy']:.3f} {row['choice_entropy']:.3f} "
                f"{row['mean_rotation']:.4f} {row['switch_rate']:.3f}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
