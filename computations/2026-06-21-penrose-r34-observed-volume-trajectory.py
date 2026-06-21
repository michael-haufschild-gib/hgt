#!/usr/bin/env python3
"""
R34: path-dependent reward trajectories -> observed-volume covariance.

NODE side: identical final rewards can have different present values when
discounting depends on the reward path.

HGT side: observed-volume covariance is tested as a trajectory observable:
the value distribution is preserved, but reordering the path changes the
volume element and can erase or flip covariance.
"""

import math
import random
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


def covariance(xs: Sequence[float], ys: Sequence[float]) -> float:
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / len(xs)


def correlation(xs: Sequence[float], ys: Sequence[float]) -> float:
    vx = covariance(xs, xs)
    vy = covariance(ys, ys)
    if vx <= 0 or vy <= 0:
        return 0.0
    return covariance(xs, ys) / math.sqrt(vx * vy)


def node_path_discount_test() -> Dict[str, object]:
    # Same final reward and same arithmetic mean, different path. The hazard
    # term depends on prior reward exposure, so valuation is trajectory-bound.
    early_high = [8.0, 8.0, 2.0, 2.0, 5.0]
    late_high = [2.0, 2.0, 8.0, 8.0, 5.0]
    assert early_high[-1] == late_high[-1]
    assert abs(sum(early_high) - sum(late_high)) < 1e-12

    def value(path: Sequence[float]) -> Tuple[float, List[float]]:
        acc = 0.0
        pv = 0.0
        weights = []
        for t, reward in enumerate(path, 1):
            acc = 0.75 * acc + 0.25 * reward
            rate = 0.03 + 0.018 * acc
            weight = math.exp(-rate * t)
            weights.append(weight)
            pv += weight * reward
        return pv, weights

    pv_early, w_early = value(early_high)
    pv_late, w_late = value(late_high)
    return {
        "final_reward_equal": early_high[-1] == late_high[-1],
        "sum_equal": sum(early_high) == sum(late_high),
        "pv_early_high": pv_early,
        "pv_late_high": pv_late,
        "pv_gap": pv_early - pv_late,
        "weights_early": w_early,
        "weights_late": w_late,
    }


def zeta_log_derivative(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(mp.diff(lambda w: mp.zeta(w), z) / mp.zeta(z))


def A_term(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(1 / z + 1 / (z - 1) - mp.log(mp.pi) / 2 + mp.digamma(z / 2) / 2)


def H(s: complex) -> complex:
    return A_term(s) + zeta_log_derivative(s)


def path_stats(values: Sequence[complex]) -> Dict[str, float]:
    o_mid = []
    speed = []
    turn = []
    for i in range(len(values) - 1):
        h0 = values[i]
        h1 = values[i + 1]
        mid_o = math.log1p(abs((h0 + h1) / 2.0))
        o_mid.append(mid_o)
        speed.append(abs(h1 - h0))
    for i in range(1, len(values) - 1):
        a = values[i] - values[i - 1]
        b = values[i + 1] - values[i]
        cross = (a.conjugate() * b).imag
        turn.append(abs(cross) / max(abs(a) * abs(b), 1e-300))
    turn_mid = [0.5 * (turn[i - 1] + turn[i]) if 0 < i < len(turn) else (turn[0] if i == 0 else turn[-1]) for i in range(len(speed))]
    return {
        "cov_o_speed": covariance(o_mid, speed),
        "corr_o_speed": correlation(o_mid, speed),
        "cov_o_turn": covariance(o_mid, turn_mid),
        "corr_o_turn": correlation(o_mid, turn_mid),
        "lag1_o": correlation(o_mid[:-1], o_mid[1:]) if len(o_mid) > 2 else 0.0,
        "lag1_speed": correlation(speed[:-1], speed[1:]) if len(speed) > 2 else 0.0,
        "median_o": median(o_mid),
        "median_speed": median(speed),
    }


def transfer_choice() -> Dict[str, object]:
    base = """
for reward path:
    weights depend on accumulated prior rewards
test: same final and same sum can produce different path value
"""
    attempts = {
        "A_observed_volume_trajectory_covariance": """
for H(t) along a sigma lane:
    volume speed = abs(H(t+dt)-H(t))
test: same value distribution under reorder has different value-volume covariance
""",
        "B_endpoint_amplitude_comparison": """
for H(t) endpoints:
    compare final abs(H)
test: endpoint amplitude predicts observed volume sign
""",
        "C_reward_memory_kernel_to_sigma": """
for sigma lanes:
    build memory kernel over previous Delta values
test: kernel top eigenvalue predicts volume covariance
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    return {"distances": distances, "chosen": min(distances, key=distances.get)}


def hgt_transfer_test() -> Dict[str, object]:
    rng = random.Random(34016)
    sigmas = [0.30, 0.50, 0.70, 1.30]
    rows = []
    for sigma in sigmas:
        ts = [18.0 + 0.12 * i for i in range(90)]
        vals = [H(complex(sigma, t)) for t in ts]
        base = path_stats(vals)
        sorted_vals = sorted(vals, key=lambda z: abs(z))
        sorted_stats = path_stats(sorted_vals)
        random_corrs = []
        random_covs = []
        for _ in range(40):
            perm = vals[:]
            rng.shuffle(perm)
            st = path_stats(perm)
            random_corrs.append(st["corr_o_speed"])
            random_covs.append(st["cov_o_speed"])
        rows.append(
            {
                "sigma": sigma,
                "base": base,
                "sorted": sorted_stats,
                "random_median_corr": median(random_corrs),
                "random_min_corr": min(random_corrs),
                "random_max_corr": max(random_corrs),
                "random_median_cov": median(random_covs),
            }
        )
    return {"rows": rows}


def step12_followup(hgt: Dict[str, object]) -> Dict[str, object]:
    sign_rows = []
    effect_rows = []
    for row in hgt["rows"]:
        base_sign = math.copysign(1, row["base"]["cov_o_speed"])
        sorted_sign = math.copysign(1, row["sorted"]["cov_o_speed"])
        random_sign = math.copysign(1, row["random_median_cov"])
        sign_rows.append((row["sigma"], base_sign, sorted_sign, random_sign))
        effect_rows.append(
            (
                row["sigma"],
                row["base"]["cov_o_speed"] / max(abs(row["random_median_cov"]), 1e-300),
                row["base"]["lag1_o"],
                row["sorted"]["lag1_o"],
            )
        )
    return {
        "sign_rows": sign_rows,
        "effect_rows": effect_rows,
        "critical_base_positive": sum(1 for r in hgt["rows"] if r["sigma"] <= 0.7 and r["base"]["cov_o_speed"] > 0),
        "critical_total": sum(1 for r in hgt["rows"] if r["sigma"] <= 0.7),
    }


def main() -> None:
    node = node_path_discount_test()
    choice = transfer_choice()
    hgt = hgt_transfer_test()
    follow = step12_followup(hgt)

    print("R34 OBSERVED_VOLUME_TRAJECTORY")
    print("NODE_RESULT")
    for key, value in node.items():
        print(f"  {key}={value}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    for row in hgt["rows"]:
        print(f"  sigma={row['sigma']:.2f}")
        print(f"    base_cov_speed={row['base']['cov_o_speed']:.9g} base_corr_speed={row['base']['corr_o_speed']:.9g}")
        print(f"    base_lag1_o={row['base']['lag1_o']:.9g} base_lag1_speed={row['base']['lag1_speed']:.9g}")
        print(f"    sorted_cov_speed={row['sorted']['cov_o_speed']:.9g} sorted_corr_speed={row['sorted']['corr_o_speed']:.9g}")
        print(f"    sorted_lag1_o={row['sorted']['lag1_o']:.9g} sorted_lag1_speed={row['sorted']['lag1_speed']:.9g}")
        print(
            f"    random_median_cov={row['random_median_cov']:.9g} "
            f"random_corr_range=({row['random_min_corr']:.9g},{row['random_max_corr']:.9g})"
        )

    print("STEP9_METHOD_RESULT")
    print("  method=4 change the viewpoint")
    print("  viewpoint_change=endpoint/final amplitude -> reward-memory / trajectory value-volume covariance")

    print("STEP12_FOLLOWUP")
    for sigma, base_sign, sorted_sign, random_sign in follow["sign_rows"]:
        print(f"  sigma={sigma:.2f} signs(base,sorted,random_median)=({base_sign:+.0f},{sorted_sign:+.0f},{random_sign:+.0f})")
    for sigma, ratio, base_lag, sorted_lag in follow["effect_rows"]:
        print(f"  sigma={sigma:.2f} base_over_random_cov={ratio:.6f} lag1_o_base={base_lag:.6f} lag1_o_sorted={sorted_lag:.6f}")
    print(f"  critical_base_positive={follow['critical_base_positive']}/{follow['critical_total']}")

    print("INTERPRETATION")
    print(
        "  Observed-volume covariance is not an endpoint-amplitude statistic, but the sign alone "
        "is too weak: random reorders preserve the positive sign and can inflate covariance. The "
        "measure-invariant claim needs a memory/effect-size passport, not only marginal value or "
        "sign controls."
    )


if __name__ == "__main__":
    main()
