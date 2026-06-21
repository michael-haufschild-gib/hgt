#!/usr/bin/env python3
"""
R35: hysteresis offset split -> phase-carrier status offset split.

NODE side: horizontal and vertical loop offsets have different meanings.

HGT side: scalar carrier height is split into horizontal seam-center offset
and vertical height offset. The nearby false statement is that a single
carrier-offset scalar is enough to decide carrier status.
"""

import math
from statistics import median
from typing import Dict, List, Sequence, Tuple

import mpmath as mp


mp.mp.dps = 35


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_hysteresis_offset_test() -> Dict[str, object]:
    xs = [math.sin(2 * math.pi * k / 200) for k in range(200)]

    def loop(h: float, v: float) -> List[float]:
        return [math.tanh(4.0 * (x - h)) + v for x in xs]

    horizontal = loop(0.18, 0.0)
    vertical = loop(0.0, 0.18)

    def estimate_offsets(ys: Sequence[float]) -> Tuple[float, float, float]:
        vertical_offset = (max(ys) + min(ys)) / 2.0
        # Estimate horizontal offset by zero crossing of y - vertical_offset.
        best_i = min(range(len(ys)), key=lambda i: abs(ys[i] - vertical_offset))
        horizontal_offset = xs[best_i]
        scalar_center = math.sqrt(horizontal_offset * horizontal_offset + vertical_offset * vertical_offset)
        return horizontal_offset, vertical_offset, scalar_center

    return {
        "horizontal_offsets_h_v_scalar": estimate_offsets(horizontal),
        "vertical_offsets_h_v_scalar": estimate_offsets(vertical),
    }


def primes_upto(n: int) -> List[int]:
    out = []
    for k in range(2, n + 1):
        for p in out:
            if p * p > k:
                break
            if k % p == 0:
                break
        else:
            out.append(k)
            continue
        if all(k % p for p in out if p * p <= k):
            out.append(k)
    return out


PRIMES = primes_upto(97)


def A_term(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(1 / z + 1 / (z - 1) - mp.log(mp.pi) / 2 + mp.digamma(z / 2) / 2)


def P_true(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(mp.diff(lambda w: mp.zeta(w), z) / mp.zeta(z))


def P_finite(s: complex, pmax: int) -> complex:
    z = complex(s)
    acc = 0j
    for p in PRIMES:
        if p > pmax:
            break
        q = p ** (-z)
        acc -= math.log(p) * q / (1.0 - q)
    return acc


def delta(A: complex, P: complex) -> float:
    return max(math.log(max(abs(A), 1e-300)), math.log(max(abs(P), 1e-300))) - math.log(max(abs(A + P), 1e-300))


def carrier_profile(t: float, kind: str, pmax: int = 47) -> List[Tuple[float, float]]:
    sigmas = [0.30 + 0.02 * i for i in range(21)]
    rows = []
    for sigma in sigmas:
        s = complex(sigma, t)
        A = A_term(s)
        P = P_true(s) if kind == "true" else P_finite(s, pmax)
        rows.append((sigma, delta(A, P)))
    return rows


def profile_offsets(profile: Sequence[Tuple[float, float]]) -> Tuple[float, float, float]:
    # Return soft carrier-centroid offset from seam, peak height, and mean height.
    peak_sigma, peak_height = max(profile, key=lambda row: row[1])
    y_max = peak_height
    weights = [math.exp(4.0 * (y - y_max)) for _x, y in profile]
    centroid = sum(w * x for w, (x, _y) in zip(weights, profile)) / sum(weights)
    mean_height = sum(y for _x, y in profile) / len(profile)
    return centroid - 0.5, peak_height, mean_height


def transfer_choice() -> Dict[str, object]:
    base = """
for hysteresis loop:
    estimate horizontal offset and vertical offset separately
test: same scalar offset can mean different physical mechanisms
"""
    attempts = {
        "A_carrier_horizontal_vertical_split": """
for Delta(sigma,t):
    estimate seam-center offset and peak-height offset separately
test: one scalar carrier gap conflates location and amplitude
""",
        "B_scalar_carrier_mean_only": """
for Delta(sigma,t):
    average over sigma and compare true/finite
test: mean carrier gap decides status
""",
        "C_phase_loop_area_offset": """
for phase loop A/P:
    compute loop area and center
test: center offset and area offset have different controls
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    return {"distances": distances, "chosen": min(distances, key=distances.get)}


def hgt_transfer_test() -> Dict[str, object]:
    zeros = [14.1347251417, 21.0220396388, 25.0108575801]
    rows = []
    for t in zeros:
        true_profile = carrier_profile(t, "true")
        finite_profile = carrier_profile(t, "finite", pmax=47)
        true_offsets = profile_offsets(true_profile)
        finite_offsets = profile_offsets(finite_profile)
        scalar_gap = abs(true_offsets[1] - finite_offsets[1]) + abs(true_offsets[2] - finite_offsets[2])
        horizontal_gap = abs(true_offsets[0] - finite_offsets[0])
        vertical_gap = abs(true_offsets[1] - finite_offsets[1])
        rows.append(
            {
                "t": t,
                "true_offsets": true_offsets,
                "finite_offsets": finite_offsets,
                "horizontal_gap": horizontal_gap,
                "vertical_gap": vertical_gap,
                "scalar_gap": scalar_gap,
            }
        )
    return {"rows": rows}


def step12_followup(hgt: Dict[str, object]) -> Dict[str, object]:
    horizontal_large = sum(1 for row in hgt["rows"] if row["horizontal_gap"] >= 0.04)
    vertical_large = sum(1 for row in hgt["rows"] if row["vertical_gap"] >= 0.1)
    return {
        "horizontal_large": horizontal_large,
        "vertical_large": vertical_large,
        "total": len(hgt["rows"]),
    }


def main() -> None:
    node = node_hysteresis_offset_test()
    choice = transfer_choice()
    hgt = hgt_transfer_test()
    follow = step12_followup(hgt)

    print("R35 CARRIER_OFFSET_SPLIT")
    print("NODE_RESULT")
    for key, value in node.items():
        print(f"  {key}={value}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    for row in hgt["rows"]:
        print(f"  t={row['t']:.10f}")
        print(f"    true(horizontal,peak,mean)={row['true_offsets']}")
        print(f"    finite(horizontal,peak,mean)={row['finite_offsets']}")
        print(
            f"    horizontal_gap={row['horizontal_gap']:.6f} "
            f"vertical_gap={row['vertical_gap']:.6f} scalar_gap={row['scalar_gap']:.6f}"
        )

    print("STEP9_METHOD_RESULT")
    print("  method=22 compare nearby false statements")
    print("  nearby_false=one scalar carrier offset is enough")

    print("STEP12_FOLLOWUP")
    print(f"  horizontal_large={follow['horizontal_large']}/{follow['total']}")
    print(f"  vertical_large={follow['vertical_large']}/{follow['total']}")

    print("INTERPRETATION")
    print(
        "  Carrier status needs offset decomposition. A finite/surrogate carrier can differ in "
        "seam location and height for different reasons; one scalar carrier gap conflates these. "
        "Report horizontal seam-center offset and vertical carrier height separately."
    )


if __name__ == "__main__":
    main()
