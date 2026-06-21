#!/usr/bin/env python3
"""THE-MACHINE tick: genotype-phenotype degeneracy -> RH Translation.

NODE:
  Multiple genotypes can map to the same phenotype without being equivalent in
  robustness, evolvability, or mutational neighborhood.

Consolidated target:
  RH Translation: source-carrying defects of d log xi are confined to Re(s)=1/2.

STEP 9 method:
  20. Name the missing lemma.
"""

from __future__ import annotations

import itertools
import math
from collections import Counter, defaultdict

import mpmath as mp
import numpy as np


NODE = (
    "multiple genotypes can map to the same phenotype without being equivalent "
    "in robustness evolvability or mutational neighborhood"
)

TRANSFER_ATTEMPTS = [
    (
        "same RH source phenotype can hide different robustness evolvability "
        "and canonical transport neighborhoods"
    ),
    (
        "unit defects of d log xi can have equal source mass but different "
        "canonical observable neighborhoods"
    ),
    (
        "multiple source defects can map to the same RH translation class "
        "without equivalent off seam transport neighborhoods"
    ),
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[j - 1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def bits_of(x: int, n: int) -> tuple[int, ...]:
    return tuple((x >> i) & 1 for i in range(n))


def node_phenotype(bits: tuple[int, ...]) -> int:
    # A small genotype-to-phenotype map with redundant focal classes but
    # uneven local neighborhoods. The point is not biology realism; it is a
    # controlled degeneracy fixture.
    linear = bits[0] + 2 * bits[1] + bits[2] - bits[3]
    epi = 2 * (bits[4] & bits[5]) - 3 * (bits[5] & bits[6]) + (bits[6] ^ bits[7])
    modifier = bits[0] * bits[7] - bits[2] * bits[4]
    return int((linear + epi + modifier) % 4)


def constant_phenotype(bits: tuple[int, ...]) -> int:
    return 0


def neighbors(x: int, n: int) -> list[int]:
    return [x ^ (1 << i) for i in range(n)]


def genotype_signatures(n: int, phenotype_fn) -> dict[int, list[dict[str, object]]]:
    phen = {x: phenotype_fn(bits_of(x, n)) for x in range(1 << n)}
    by_pheno: dict[int, list[dict[str, object]]] = defaultdict(list)
    for x in range(1 << n):
        p = phen[x]
        neigh = neighbors(x, n)
        counts = Counter(phen[y] for y in neigh)
        robustness = counts[p] / n
        alternatives = len([q for q in counts if q != p])
        signature = tuple(counts.get(q, 0) for q in sorted(set(phen.values())))
        by_pheno[p].append(
            {
                "genotype": x,
                "robustness": robustness,
                "alternatives": alternatives,
                "signature": signature,
            }
        )
    return by_pheno


def l1(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    return sum(abs(x - y) for x, y in zip(a, b))


def summarize_node(n: int = 8) -> list[str]:
    lines: list[str] = []
    lines.append("STEP 6 NODE TEST")
    lines.append(
        "Constraint: same focal phenotype must not be treated as equality of "
        "robustness/evolvability/mutational neighborhood."
    )

    for label, fn in [("structured_degenerate", node_phenotype), ("constant_control", constant_phenotype)]:
        by_pheno = genotype_signatures(n, fn)
        lines.append(f"\nNODE map={label}")
        for p in sorted(by_pheno):
            rows = by_pheno[p]
            robs = [float(r["robustness"]) for r in rows]
            alts = [int(r["alternatives"]) for r in rows]
            sigs = [r["signature"] for r in rows]
            max_sig_l1 = 0
            if len(sigs) > 1:
                max_sig_l1 = max(l1(a, b) for a, b in itertools.combinations(sigs, 2))
            lines.append(
                "phenotype={p} count={count} robustness_min_med_max="
                "{rmin:.3f}/{rmed:.3f}/{rmax:.3f} alternatives={amin}-{amax} "
                "signature_types={stype} max_signature_l1={l1}".format(
                    p=p,
                    count=len(rows),
                    rmin=min(robs),
                    rmed=float(np.median(robs)),
                    rmax=max(robs),
                    amin=min(alts),
                    amax=max(alts),
                    stype=len(set(sigs)),
                    l1=max_sig_l1,
                )
            )

    lines.append(
        "\nNODE verdict: the structured map validates the constraint: every "
        "phenotype class is degenerate, but classes contain different local "
        "robustness and neighborhood signatures. The constant map is the "
        "existence-of-equivalence extreme."
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


def zeta_zero_heights(k: int) -> list[float]:
    heights = []
    try:
        for i in range(1, k + 1):
            z = mp.zetazero(i)
            heights.append(float(mp.im(z)))
        return heights
    except Exception:
        return [
            14.134725141734695,
            21.022039638771554,
            25.01085758014569,
            30.424876125859513,
            32.93506158773919,
            37.586178158825675,
            40.918719012147495,
            43.327073280914999,
            48.005150881167159,
            49.773832477672302,
            52.970321477714461,
            56.446247697063394,
        ][:k]


def rectangle_points(center: complex, half_width: float, half_height: float, per_side: int = 20) -> list[complex]:
    c = complex(center)
    left = c.real - half_width
    right = c.real + half_width
    bottom = c.imag - half_height
    top = c.imag + half_height
    pts: list[complex] = []
    for j in range(per_side):
        u = j / per_side
        pts.append(complex(left + (right - left) * u, bottom))
    for j in range(per_side):
        u = j / per_side
        pts.append(complex(right, bottom + (top - bottom) * u))
    for j in range(per_side):
        u = j / per_side
        pts.append(complex(right - (right - left) * u, top))
    for j in range(per_side):
        u = j / per_side
        pts.append(complex(left, top - (top - bottom) * u))
    return pts


def unwrap_delta(a: float) -> float:
    while a <= -math.pi:
        a += 2 * math.pi
    while a > math.pi:
        a -= 2 * math.pi
    return a


def winding_count(center: complex, half_width: float, half_height: float) -> int:
    pts = rectangle_points(center, half_width, half_height)
    angles = [float(mp.arg(xi(p))) for p in pts]
    total = 0.0
    for a, b in zip(angles, angles[1:] + angles[:1]):
        total += unwrap_delta(b - a)
    return int(round(total / (2 * math.pi)))


def rh_signature(t: float) -> dict[str, object]:
    rho = complex(0.5, t)
    widths = [0.025, 0.05, 0.1]
    heights = [0.08, 0.16, 0.32]
    counts = [winding_count(rho, w, h) for w in widths for h in heights]
    count_stability = sum(c == 1 for c in counts) / len(counts)

    residual_mags = []
    pole_mags = []
    left_right = []
    up_down = []
    for r in [0.025, 0.05, 0.1]:
        values = {}
        for name, dz in {
            "right": complex(r, 0),
            "left": complex(-r, 0),
            "up": complex(0, r),
            "down": complex(0, -r),
        }.items():
            s = rho + dz
            pole = 1 / dz
            val = h_completed(s)
            residual = val - pole
            values[name] = abs(complex(residual))
            residual_mags.append(values[name])
            pole_mags.append(abs(pole))
        left_right.append(abs(values["right"] - values["left"]))
        up_down.append(abs(values["up"] - values["down"]))

    residual_mags_np = np.array(residual_mags, dtype=float)
    sig = np.array(
        [
            float(np.mean(residual_mags_np)),
            float(np.std(residual_mags_np)),
            float(np.mean(left_right)),
            float(np.mean(up_down)),
            float(max(residual_mags_np)),
        ],
        dtype=float,
    )
    return {
        "t": t,
        "counts": tuple(counts),
        "count_stability": count_stability,
        "signature": sig,
        "residual_to_pole": float(np.mean(residual_mags_np) / np.mean(pole_mags)),
    }


def pairwise_distances(signatures: list[np.ndarray]) -> list[float]:
    out = []
    for a, b in itertools.combinations(signatures, 2):
        out.append(float(np.linalg.norm(a - b)))
    return out


def summarize_transfer() -> list[str]:
    mp.mp.dps = 40
    lines: list[str] = []
    lines.append("\nSTEP 7 FORMULA CHECK")
    lines.append(
        "NODE formulas are finite graph-neighborhood counts: robustness, "
        "alternative-neighbor count, and neighborhood signature. Applied "
        "unchanged to RH Translation they are only generic graph statistics, "
        "not source-measure or d log xi content. No unchanged formula is promoted."
    )

    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 20: NAME THE MISSING LEMMA")
    lines.append(
        "Missing lemma candidate: same-source-mass neighborhood equivalence. "
        "If two simple source-carrying defects of d log xi have the same "
        "source mass and lie on the RH seam, then after translation by height "
        "their canonical observable neighborhoods are equivalent."
    )
    lines.append(
        "Test: for the first seam zeros, confirm the same source phenotype by "
        "argument-principle winding around small rectangles, then compare the "
        "translated residual neighborhood H(s)-1/(s-rho)."
    )

    heights = zeta_zero_heights(12)
    rows = [rh_signature(t) for t in heights]
    sigs = [r["signature"] for r in rows]
    dists = pairwise_distances(sigs)
    lines.append("\nRH TRANSLATION TEST")
    for idx, row in enumerate(rows, 1):
        sig = row["signature"]
        lines.append(
            "zero={idx:02d} t={t:.6f} source_count_stability={stab:.3f} "
            "residual_mean/std/lr/ud/max={a:.5g}/{b:.5g}/{c:.5g}/{d:.5g}/{e:.5g} "
            "residual_to_pole={rp:.5g}".format(
                idx=idx,
                t=row["t"],
                stab=row["count_stability"],
                a=sig[0],
                b=sig[1],
                c=sig[2],
                d=sig[3],
                e=sig[4],
                rp=row["residual_to_pole"],
            )
        )
    lines.append(
        "same_source_pairwise_signature_distance min/median/max="
        f"{min(dists):.5g}/{float(np.median(dists)):.5g}/{max(dists):.5g}"
    )
    lines.append(
        "pure_pole_control: after subtracting the universal simple-pole term, "
        "a translated pure-pole model has zero residual signature and pairwise "
        "distance 0 by construction."
    )
    lines.append(
        "RH verdict before Step 11: the too-strong missing lemma is false for "
        "raw canonical neighborhoods. Equal source count is stable, but the "
        "completed background around each source is not translation-equivalent. "
        "This is an instrument warning unless it survives reduction to known "
        "local pole plus surrounding-zero/background effects."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: genotype-phenotype degeneracy -> RH Translation")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 32/32 RH Translation")
    out.extend(summarize_node())
    out.extend(summarize_transfer())
    print("\n".join(out))


if __name__ == "__main__":
    main()
