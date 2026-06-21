#!/usr/bin/env python3
"""
R31: Ward-identity context -> xi mirror-context fragility.

NODE side: individual source/photon components can violate a Ward constraint while
the full context satisfies it.

HGT side: the completed log derivative H=xi'/xi satisfies the mirror identity
H(s)+H(1-s)=0 only in the full A+P context. Phase-context scrambling of P
preserves local magnitudes but destroys the identity.
"""

import math
import random
from statistics import median
from typing import Dict, List, Sequence, Tuple

import mpmath as mp


mp.mp.dps = 40


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def dot(a: Sequence[float], b: Sequence[float]) -> float:
    return sum(x * y for x, y in zip(a, b))


def add_vecs(vectors: Sequence[Sequence[float]]) -> List[float]:
    return [sum(v[i] for v in vectors) for i in range(len(vectors[0]))]


def node_ward_test() -> Dict[str, object]:
    rng = random.Random(31017)
    q_raw = [0.7, -0.2, 0.5, 0.4]
    q_norm = math.sqrt(dot(q_raw, q_raw))
    q = [x / q_norm for x in q_raw]

    longitudinal = [1.2, -0.7, -0.5]  # sums to zero only in the full context
    components = []
    for ell in longitudinal:
        raw = [rng.uniform(-1, 1) for _ in range(4)]
        transverse = [raw[i] - dot(raw, q) * q[i] for i in range(4)]
        components.append([transverse[i] + ell * q[i] for i in range(4)])

    total = add_vecs(components)
    dropped_contact = add_vecs(components[:2])
    return {
        "component_residuals": [dot(q, c) for c in components],
        "total_residual": dot(q, total),
        "drop_contact_residual": dot(q, dropped_contact),
        "max_component_abs": max(abs(dot(q, c)) for c in components),
    }


def zeta_log_derivative(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(mp.diff(lambda w: mp.zeta(w), z) / mp.zeta(z))


def A_term(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(1 / z + 1 / (z - 1) - mp.log(mp.pi) / 2 + mp.digamma(z / 2) / 2)


def P_term(s: complex) -> complex:
    return zeta_log_derivative(s)


def angle(z: complex) -> float:
    return math.atan2(z.imag, z.real)


def wrap(theta: float) -> float:
    while theta <= -math.pi:
        theta += 2 * math.pi
    while theta > math.pi:
        theta -= 2 * math.pi
    return theta


def phase_mix(z: complex, target_angle: float, alpha: float) -> complex:
    theta = angle(z)
    new_theta = theta + alpha * wrap(target_angle - theta)
    return abs(z) * complex(math.cos(new_theta), math.sin(new_theta))


def log10_ratio(num: float, den: float) -> float:
    return math.log10(max(num, 1e-300) / max(den, 1e-300))


def sample_points() -> List[complex]:
    sigmas = [0.30, 0.40, 0.50, 0.60, 0.70]
    ts = [18.0 + 0.25 * k for k in range(25)]
    return [complex(sigma, t) for sigma in sigmas for t in ts]


def transfer_choice() -> Dict[str, object]:
    base = """
for each component J_i:
    residual_i = q dot J_i
full_residual = q dot sum_i J_i
test: parts violate Ward; full source context cancels
"""
    attempts = {
        "A_xi_mirror_ward_residual": """
for each point s:
    residual = H(s) + H(1-s), H=A+P
scramble phase context of P while preserving magnitudes
test: components violate mirror Ward; full completed context cancels
""",
        "B_phase_delta_context_decay": """
for each point s:
    delta = max(logabs(A), logabs(P)) - logabs(A+P)
scramble phase context in blocks
test: median delta decays under scrambling
""",
        "C_cross_lane_covariance_context": """
for each sigma lane:
    kernel = covariance(phase_defect_sigma, phase_defect_sigma_prime)
scramble lane labels
test: top eigenvalue decays under context erasure
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    chosen = min(distances, key=distances.get)
    return {"distances": distances, "chosen": chosen}


def hgt_context_test(seed: int = 431) -> Dict[str, object]:
    points = sample_points()
    mirrors = [1 - s for s in points]
    A = [A_term(s) for s in points]
    P = [P_term(s) for s in points]
    Am = [A_term(s) for s in mirrors]
    Pm = [P_term(s) for s in mirrors]
    H = [a + p for a, p in zip(A, P)]
    Hm = [a + p for a, p in zip(Am, Pm)]

    full_residuals = [abs(h + hm) for h, hm in zip(H, Hm)]
    full_scales = [abs(h) + abs(hm) for h, hm in zip(H, Hm)]
    A_residuals = [abs(a + am) for a, am in zip(A, Am)]
    P_residuals = [abs(p + pm) for p, pm in zip(P, Pm)]
    comp_scales = [abs(a) + abs(am) + abs(p) + abs(pm) for a, am, p, pm in zip(A, Am, P, Pm)]

    rng = random.Random(seed)
    perm = list(range(len(points)))
    rng.shuffle(perm)
    target_angles = [angle(P[j]) for j in perm]
    target_angles_m = [angle(Pm[j]) for j in perm]

    alpha_rows = []
    for alpha in [0.0, 0.05, 0.10, 0.20, 0.35, 0.50, 0.75, 1.0]:
        P_alpha = [phase_mix(p, target_angles[i], alpha) for i, p in enumerate(P)]
        Pm_alpha = [phase_mix(p, target_angles_m[i], alpha) for i, p in enumerate(Pm)]
        H_alpha = [a + p for a, p in zip(A, P_alpha)]
        Hm_alpha = [a + p for a, p in zip(Am, Pm_alpha)]
        residual = [abs(h + hm) for h, hm in zip(H_alpha, Hm_alpha)]
        scale = [abs(h) + abs(hm) for h, hm in zip(H_alpha, Hm_alpha)]
        delta = [
            max(math.log(max(abs(a), 1e-300)), math.log(max(abs(p), 1e-300)))
            - math.log(max(abs(a + p), 1e-300))
            for a, p in zip(A, P_alpha)
        ]
        alpha_rows.append(
            (
                alpha,
                median(log10_ratio(r, sc) for r, sc in zip(residual, scale)),
                median(delta),
                max(log10_ratio(r, sc) for r, sc in zip(residual, scale)),
            )
        )

    return {
        "n_points": len(points),
        "full_median_log10_residual_ratio": median(log10_ratio(r, sc) for r, sc in zip(full_residuals, full_scales)),
        "full_max_log10_residual_ratio": max(log10_ratio(r, sc) for r, sc in zip(full_residuals, full_scales)),
        "A_component_median_log10_residual_ratio": median(log10_ratio(r, sc) for r, sc in zip(A_residuals, comp_scales)),
        "P_component_median_log10_residual_ratio": median(log10_ratio(r, sc) for r, sc in zip(P_residuals, comp_scales)),
        "alpha_rows": alpha_rows,
    }


def step12_followup(trials: int = 12) -> Dict[str, object]:
    rows = []
    for seed in range(500, 500 + trials):
        result = hgt_context_test(seed)
        alpha_rows = result["alpha_rows"]
        residuals = [row[1] for row in alpha_rows]
        monotone_breaks = sum(1 for a, b in zip(residuals, residuals[1:]) if b < a - 1e-9)
        total_lift = residuals[-1] - residuals[0]
        rows.append((seed, monotone_breaks, total_lift, residuals[0], residuals[-1]))
    return {
        "rows": rows,
        "monotone_passes": sum(1 for _seed, breaks, _lift, _start, _end in rows if breaks == 0),
        "positive_lifts": sum(1 for _seed, _breaks, lift, _start, _end in rows if lift > 2.0),
    }


def apply_method_12_find_invariant(hgt: Dict[str, object]) -> Dict[str, object]:
    alpha_rows = hgt["alpha_rows"]
    start = alpha_rows[0][1]
    end = alpha_rows[-1][1]
    return {
        "method": "12 find an invariant",
        "invariant": "completed FE/Ward mirror residual H(s)+H(1-s)",
        "full_context_log10_ratio": start,
        "scrambled_context_log10_ratio": end,
        "residual_lift_dex": end - start,
    }


def main() -> None:
    node = node_ward_test()
    choice = transfer_choice()
    hgt = hgt_context_test()
    method = apply_method_12_find_invariant(hgt)
    follow = step12_followup()

    print("R31 WARD_CONTEXT_FRAGILITY")
    print("NODE_RESULT")
    print(f"  component_residuals={node['component_residuals']}")
    print(f"  total_residual={node['total_residual']:.12e}")
    print(f"  drop_contact_residual={node['drop_contact_residual']:.12e}")
    print(f"  max_component_abs={node['max_component_abs']:.12e}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    print(f"  n_points={hgt['n_points']}")
    print(f"  full_median_log10_residual_ratio={hgt['full_median_log10_residual_ratio']:.6f}")
    print(f"  full_max_log10_residual_ratio={hgt['full_max_log10_residual_ratio']:.6f}")
    print(f"  A_component_median_log10_residual_ratio={hgt['A_component_median_log10_residual_ratio']:.6f}")
    print(f"  P_component_median_log10_residual_ratio={hgt['P_component_median_log10_residual_ratio']:.6f}")
    print("  alpha median_log10_FE_residual_ratio median_delta max_log10_FE_residual_ratio")
    for alpha, med_resid, med_delta, max_resid in hgt["alpha_rows"]:
        print(f"  alpha={alpha:.2f} med_resid={med_resid:.6f} med_delta={med_delta:.6f} max_resid={max_resid:.6f}")

    print("STEP9_METHOD_RESULT")
    for key, value in method.items():
        print(f"  {key}={value}")

    print("STEP12_FOLLOWUP")
    print(f"  monotone_passes={follow['monotone_passes']}/{len(follow['rows'])}")
    print(f"  positive_lifts_gt_2dex={follow['positive_lifts']}/{len(follow['rows'])}")
    for seed, breaks, lift, start, end in follow["rows"]:
        print(f"  seed={seed} monotone_breaks={breaks} lift={lift:.6f} start={start:.6f} end={end:.6f}")

    print("INTERPRETATION")
    print(
        "  Full-context mirror cancellation is many orders smaller than component residuals. "
        "Phase-context scrambling preserves local P magnitudes but rapidly destroys the mirror "
        "Ward residual. The decay is strong but not strictly monotone for every random path, so "
        "context fragility should be stated as a residual-lift gate, not a pointwise monotonicity law."
    )


if __name__ == "__main__":
    main()
