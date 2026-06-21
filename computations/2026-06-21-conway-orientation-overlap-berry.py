#!/usr/bin/env python3
"""THE-MACHINE tick: hidden sheet orientation overlap -> Berry seam layer."""

from __future__ import annotations

import math
import runpy

import numpy as np


NODE = "Orientation data in currents can be lost or flipped when hidden sheets overlap in projection"
TARGET = "31/32 Berry Seam Layer"
METHOD = "17. Change representation"

TRANSFER_ATTEMPTS = [
    "Berry mirror lanes must be read as oriented currents before projection",
    "hidden overlapping sheets become mirror-lane Berry phase overlap",
    "completion moves Berry obstruction into orientation data lost by projection",
]

BASE = runpy.run_path("computations/2026-06-21-conway-kam-resolution-berry-seam.py")
first_primes = BASE["first_primes"]
field_value = BASE["field_value"]
ZEROS = BASE["ZEROS"]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur[-1:] and cur
    return prev[-1]


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: projected sheets can erase orientation"]
    lines.append("sheet_pair scalar_multiplicity oriented_current projected_signed")
    cases = [
        ("same_orientation", 1.0, 1.0),
        ("opposite_orientation", 1.0, -1.0),
        ("imbalanced_hidden", 1.0, -0.7),
    ]
    for name, a, b in cases:
        scalar = abs(a) + abs(b)
        oriented = a + b
        projected_signed = math.copysign(scalar, oriented) if abs(oriented) > 1e-12 else 0.0
        lines.append(f"{name:20s} {scalar:.3f} {oriented:+.3f} {projected_signed:+.3f}")
    lines.append(
        "NODE verdict: projection preserves scalar multiplicity but can cancel or flip oriented current."
    )
    return lines


def lane_pair(kind: str, center: float, zero_t: float, delta: float, samples: int, primes, rng):
    left_sigma = center - delta
    right_sigma = center + delta
    width = 0.55
    ts = np.linspace(zero_t - width, zero_t + width, samples)
    weight = np.exp(-((ts - zero_t) / (0.42 * width + 1e-12)) ** 2)
    left = 0.0 + 0.0j
    right = 0.0 + 0.0j
    for t, w in zip(ts, weight):
        left += w * field_value(kind, complex(left_sigma, float(t)), primes, rng)
        right += w * field_value(kind, complex(right_sigma, float(t)), primes, rng)
    return left / float(np.sum(weight)), right / float(np.sum(weight))


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Current/varifold projection formulas do not apply unchanged. The transfer keeps the "
        "constraint: mirror-lane Berry data must be represented as oriented two-path data before "
        "projecting to scalar amplitudes."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    _, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 17: CHANGE REPRESENTATION")
    lines.append("Represent mirror lanes as complex oriented currents L,R. Compare signed current Im(conj(L)R), even projection |L+R|^2, and odd/Berry projection |L-R|^2.")
    primes = first_primes(160)
    lines.append("kind center signed_current even_power odd_power imbalance rel_phase projection_loses_orientation")
    lost = 0
    total = 0
    for center in [0.50, 0.58]:
        for kind in ["bare", "xi", "finite_xi", "random_xi"]:
            vals = []
            for z in ZEROS:
                rng = np.random.default_rng(2606216711 + int(1000 * center) + int(10 * z) + len(kind))
                l, r = lane_pair(kind, center, z, 0.16, 96, primes, rng)
                signed = float((np.conj(l) * r).imag)
                even = abs(l + r) ** 2
                odd = abs(l - r) ** 2
                imb = abs(abs(l) - abs(r)) / (abs(l) + abs(r) + 1e-300)
                phase = abs(math.atan2((l / (r + 1e-300)).imag, (l / (r + 1e-300)).real))
                loses = int(abs(signed) > 0.05 * (abs(l) * abs(r) + 1e-300) and imb < 0.05)
                vals.append((signed, even, odd, imb, phase, loses))
            mean = np.asarray(vals, dtype=float)
            lost += int(np.mean(mean[:, 5]) > 0.5)
            total += 1
            lines.append(
                f"{kind:9s} {center:.2f} {float(np.mean(mean[:,0])):+.6f} {float(np.mean(mean[:,1])):.6f} "
                f"{float(np.mean(mean[:,2])):.6f} {float(np.mean(mean[:,3])):.6f} "
                f"{float(np.mean(mean[:,4])):.6f} {int(np.mean(mean[:,5]) > 0.5)}"
            )
    lines.append("")
    lines.append(f"ORIENTATION_LOSS_ROWS {lost}/{total}")
    lines.append(
        "Interpretation: if only completed seam rows show balanced magnitudes plus nonzero signed "
        "current, then projection/overlap loses exactly the existing Berry relative-phase channel."
    )
    return lines


def main() -> None:
    out = []
    out.append("THE-MACHINE tick: orientation overlap -> Berry seam")
    out.append(f"NODE: {NODE}")
    out.append(f"Standing-order target: {TARGET}")
    out.append(f"STEP 9 method: {METHOD}")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
