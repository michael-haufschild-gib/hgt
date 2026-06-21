#!/usr/bin/env python3
"""THE-MACHINE tick: enhanced gauge symmetry strata -> where zeros live.

NODE:
  Singular strata from enhanced gauge symmetry.

Consolidated target:
  Where the zeros live in the geometry.

STEP 9 method:
  1. Split it into subclaims.
"""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


NODE = "singular strata from enhanced gauge symmetry"
TRANSFER_ATTEMPTS = [
    "zero source strata are enhanced symmetry loci of completed transport",
    "zeros live where the local source stabilizer jumps",
    "critical zero geometry has singular strata from pole isotropy enhancement",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb))
            )
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    lines = ["STEP 6 NODE TEST: stabilizer jump in a conjugation quotient"]
    lines.append(
        "Hermitian 2x2 matrices under unitary conjugation have orbit type "
        "controlled by eigenvalue multiplicity. Repeated eigenvalues have "
        "larger stabilizer and form a singular quotient stratum."
    )
    lines.append("a b gap centralizer_dim orbit_dim stratum")
    for a, b in [(-1, 1), (0, 1), (1, 1), (2, 2), (2, 3)]:
        gap = abs(a - b)
        if gap == 0:
            cdim = 4
            orbit = 0
            stratum = "enhanced"
        else:
            cdim = 2
            orbit = 2
            stratum = "generic"
        lines.append(f"{a: .1f} {b: .1f} {gap:.1f} {cdim:d} {orbit:d} {stratum}")
    lines.append(
        "NODE verdict: the singular stratum is not high amplitude; it is a "
        "rank/stabilizer jump at eigenvalue collision."
    )
    return lines


def xi(s: complex) -> complex:
    z = mp.mpc(s)
    return 0.5 * z * (z - 1) * mp.power(mp.pi, -z / 2) * mp.gamma(z / 2) * mp.zeta(z)


def h_completed(s: complex) -> complex:
    z = mp.mpc(s)
    return (
        1 / z
        + 1 / (z - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(z / 2) / 2
        + mp.diff(lambda w: mp.zeta(w), z) / mp.zeta(z)
    )


def gamma_part(s: complex) -> complex:
    z = mp.mpc(s)
    return -mp.log(mp.pi) / 2 + mp.digamma(z / 2) / 2


def zeta_zero_heights(k: int) -> list[float]:
    return [float(mp.im(mp.zetazero(i))) for i in range(1, k + 1)]


def unwrap_delta(a: float) -> float:
    while a <= -math.pi:
        a += 2 * math.pi
    while a > math.pi:
        a -= 2 * math.pi
    return a


def circle_points(center: complex, radius: float, n: int = 96) -> list[complex]:
    return [center + radius * complex(math.cos(2 * math.pi * j / n), math.sin(2 * math.pi * j / n)) for j in range(n)]


def winding(center: complex, radius: float) -> int:
    angles = [float(mp.arg(xi(p))) for p in circle_points(center, radius)]
    total = 0.0
    for a, b in zip(angles, angles[1:] + angles[:1]):
        total += unwrap_delta(b - a)
    return int(round(total / (2 * math.pi)))


def pole_isotropy(center: complex, radius: float, mode: str) -> tuple[float, float]:
    vals = []
    for p in circle_points(center, radius):
        if mode == "completed":
            h = h_completed(p)
        elif mode == "gamma_only":
            h = gamma_part(p)
        elif mode == "pure_pole":
            h = 1 / (p - center)
        else:
            raise ValueError(mode)
        vals.append(abs((p - center) * complex(h)))
    arr = np.array(vals, dtype=float)
    return float(np.mean(arr)), float(np.std(arr) / (np.mean(arr) + 1e-300))


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Gauge-stabilizer formulas do not apply unchanged. The transfer uses "
        "completed-log-derivative source count and local pole isotropy near "
        "known zero heights."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 1: SPLIT INTO SUBCLAIMS")
    lines.append("Subclaim A: loop source count jumps at zero strata.")
    lines.append("Subclaim B: after multiplying by local radius, completed H has near-pole isotropy close to the pure-pole model at small radius.")
    lines.append("Subclaim C: larger radii/background break exact isotropy, so this must reduce to the local source model unless extra structure remains.")
    lines.append("zero radius winding completed_mean completed_cv pure_cv gamma_mean gamma_cv")
    for idx, t in enumerate(zeta_zero_heights(8), 1):
        center = complex(0.5, t)
        for radius in [0.01, 0.03, 0.08, 0.16]:
            w = winding(center, radius)
            cm, cc = pole_isotropy(center, radius, "completed")
            _, pc = pole_isotropy(center, radius, "pure_pole")
            gm, gc = pole_isotropy(center, radius, "gamma_only")
            lines.append(
                f"{idx:02d} {radius:.2f} {w:d} {cm:.6f} {cc:.6f} {pc:.6f} {gm:.6f} {gc:.6f}"
            )
    lines.append(
        "\nTransfer verdict before Step 11: source count and small-radius "
        "isotropy behave exactly like simple local poles. Background breaks "
        "isotropy at larger radius, but no new zero-geometry invariant is "
        "visible yet."
    )
    return lines


def main() -> None:
    mp.mp.dps = 40
    out: list[str] = []
    out.append("THE-MACHINE tick: enhanced gauge symmetry strata -> where zeros live")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 6/32 Where the zeros live in the geometry")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
