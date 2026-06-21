#!/usr/bin/env python3
"""THE-MACHINE run: biofilm partition coefficients and weld-density normalization."""

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
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_density_normalization() -> None:
    """Validate the NODE constraint on a toy biofilm sorption model."""
    rng = np.random.default_rng(219019)
    rows = []
    for _ in range(160):
        dry_mass = rng.lognormal(mean=0.0, sigma=0.65)
        eps_frac = rng.beta(2.0, 5.0)
        dna_frac = rng.beta(1.5, 7.0)
        mineral_frac = rng.beta(1.2, 8.0)
        thickness = rng.lognormal(mean=0.0, sigma=0.45)
        porosity = float(np.clip(rng.normal(0.65, 0.12), 0.25, 0.92))
        surface = dry_mass ** (2.0 / 3.0) * (1.0 + 0.55 * porosity)
        binding_sites = dry_mass * (eps_frac + 1.8 * dna_frac + 2.4 * mineral_frac)
        c_free = 0.35 + 0.20 * rng.random()
        k_true = 4.0
        sorbed = k_true * c_free * binding_sites
        rows.append((dry_mass, binding_sites, thickness, surface, c_free, sorbed))

    arr = np.asarray(rows)
    dry_mass, binding_sites, thickness, surface, c_free, sorbed = arr.T
    normalizers = {
        "dry_mass": dry_mass,
        "volume": dry_mass * thickness,
        "surface": surface,
        "binding_sites": binding_sites,
    }
    print("NODE simulation: apparent partition coefficient depends on density normalization")
    print("normalizer mean cv corr_with_dry_mass corr_with_binding_sites")
    for name, norm in normalizers.items():
        kapp = sorbed / np.maximum(c_free * norm, 1e-12)
        cv = float(np.std(kapp) / max(np.mean(kapp), 1e-12))
        corr_dry = float(np.corrcoef(kapp, dry_mass)[0, 1])
        corr_sites = float(np.corrcoef(kapp, binding_sites)[0, 1])
        print(f"{name:13s} {np.mean(kapp):8.4f} {cv:8.4f} {corr_dry:8.4f} {corr_sites:8.4f}")
    print("constraint: binding-site normalization recovers the invariant coefficient; bulk density bases do not.")


def run_levenshtein() -> str:
    node_sig = "apparent partition coefficients depend strongly on biofilm density normalization"
    candidates = [
        "apparent phase partition coefficients depend strongly on strip density normalization",
        "phase defect coefficient depends on sigma lane normalization",
        "zero shadow partition ratios depend on carrier density normalization",
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
    return best[2]


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


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes, rng):
    rows = []
    for t in np.linspace(window[0], window[1], samples, endpoint=False):
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
        weld = g + p
        rows.append(
            (
                phase_defect(g, p),
                math.log1p(abs(weld)),
                math.log1p(abs(p)),
                math.log1p(abs(g)),
                math.atan2(weld.imag, weld.real),
            )
        )
    return np.asarray(rows)


def component_count(mask: np.ndarray) -> int:
    n = 0
    prev = False
    for item in mask:
        cur = bool(item)
        if cur and not prev:
            n += 1
        prev = cur
    return n


def ht_density_normalization(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    windows = [(100.0, 170.0), (500.0, 570.0)]
    print("\nStanding-order consolidated target: The Weld")
    print("Target content: Source A archimedean term A and Source B prime term P held together in H=A+P.")
    print("STEP8 transfer: apparent weld partition coefficients under strip-density normalizers")
    print("STEP9 method 15: strengthen the conjecture.")
    print(
        "Strengthened gate: a non-reducing weld finding must keep true/control separation under "
        "time, event, component, prime-amplitude, and weld-amplitude normalizations."
    )
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print(
        "kind sigma window bound free k_time k_event k_component k_prime_amp k_weld_amp "
        "swing event_to_time component_to_event"
    )
    for window in windows:
        window_name = f"{int(window[0])}-{int(window[1])}"
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite", "random"]:
                seed = 219700 + int(10 * window[0]) + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind]
                rng = np.random.default_rng(seed)
                tr = trace(kind, sigma, window, samples, primes, rng)
                defect = tr[:, 0]
                excess = np.maximum(defect - 0.8, 0.0)
                mask = excess > 0.0
                bound = float(np.sum(excess))
                free = float(np.sum(tr[:, 1]) + 1e-12)
                n_time = float(len(excess))
                n_event = float(np.sum(mask))
                n_component = float(component_count(mask))
                prime_amp = float(np.sum(tr[:, 2]) + 1e-12)
                weld_amp = float(np.sum(tr[:, 1]) + 1e-12)
                norms = {
                    "time": n_time,
                    "event": max(n_event, 1.0),
                    "component": max(n_component, 1.0),
                    "prime_amp": prime_amp,
                    "weld_amp": weld_amp,
                }
                kapp = {name: bound / (free * norm) for name, norm in norms.items()}
                vals = np.asarray(list(kapp.values()))
                swing = float(np.max(vals) / max(np.min(vals), 1e-15)) if bound > 0 else 1.0
                event_to_time = kapp["event"] / max(kapp["time"], 1e-15)
                component_to_event = kapp["component"] / max(kapp["event"], 1e-15)
                print(
                    f"{kind:6s} {sigma:.1f} {window_name:7s} {bound:9.4f} {free:9.4f} "
                    f"{kapp['time']:.6f} {kapp['event']:.6f} {kapp['component']:.6f} "
                    f"{kapp['prime_amp']:.6f} {kapp['weld_amp']:.6f} {swing:8.3f} "
                    f"{event_to_time:8.3f} {component_to_event:8.3f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_density_normalization()
    run_levenshtein()
    print(
        "\nSTEP7 formula check: K_app = sorbed / (C_free * density_basis). "
        "Applied unchanged to HT it is generic normalization arithmetic, not continuum/differential weld content."
    )
    ht_density_normalization(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
