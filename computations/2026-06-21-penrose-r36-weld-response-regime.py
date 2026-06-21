#!/usr/bin/env python3
"""
R36: phase-response regime -> native weld morphism passport.

NODE side: phase-response curves can switch type with perturbation strength.

HGT side: perturb prime phase in the completed weld A+P and classify whether
the carrier response is fold-free/linearized or fold-forming/reset-like. This
is a morphism-regime gate for M+ rather than a new theorem about zeta.
"""

import math
from typing import Dict, List, Sequence, Tuple

import mpmath as mp


mp.mp.dps = 35


def wrap(x: float) -> float:
    while x <= -math.pi:
        x += 2 * math.pi
    while x > math.pi:
        x -= 2 * math.pi
    return x


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_prc_test() -> Dict[str, object]:
    eps_values = [0.2, 0.8, 1.0, 1.2, 1.8]
    rows = []
    for eps in eps_values:
        min_deriv = 1.0 - eps
        fold = eps > 1.0
        # Winding degree stays 1, but the response map ceases to be monotone.
        rows.append((eps, min_deriv, fold))
    return {"rows": rows}


def zeta_log_derivative(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(mp.diff(lambda w: mp.zeta(w), z) / mp.zeta(z))


def A_term(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(1 / z + 1 / (z - 1) - mp.log(mp.pi) / 2 + mp.digamma(z / 2) / 2)


def delta(A: complex, P: complex) -> float:
    return max(math.log(max(abs(A), 1e-300)), math.log(max(abs(P), 1e-300))) - math.log(max(abs(A + P), 1e-300))


def transfer_choice() -> Dict[str, object]:
    base = """
for phase oscillator:
    response map theta -> theta + eps*sin(theta)
test: eps<=1 fold-free; eps>1 reset-like fold regime
"""
    attempts = {
        "A_weld_morphism_response_regime": """
for weld samples A,P:
    perturb prime phase by eps*sin(relative_phase)
test: small eps is fold-free carrier morphism; large eps creates reset/fold response
""",
        "B_scalar_epsilon_cutoff": """
for carrier Delta:
    sweep epsilon and measure mean absolute change
test: choose a scalar cutoff for acceptable perturbation size
""",
        "C_category_object_count": """
for M+ objects:
    count generators partial_s and sigma_p
test: generator count changes under perturbation strength
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    return {"distances": distances, "chosen": min(distances, key=distances.get)}


def response_curve(eps: float) -> Dict[str, float]:
    samples = []
    for sigma in [0.35, 0.45, 0.50, 0.55, 0.65]:
        for k in range(72):
            t = 18.0 + 0.12 * k
            s = complex(sigma, t)
            A = A_term(s)
            P = zeta_log_derivative(s)
            phi = wrap(math.atan2(P.imag, P.real) - math.atan2(A.imag, A.real))
            d0 = delta(A, P)
            P2 = P * complex(math.cos(eps * math.sin(phi)), math.sin(eps * math.sin(phi)))
            d1 = delta(A, P2)
            samples.append((phi, d1 - d0))
    samples.sort(key=lambda row: row[0])
    slopes = []
    folds = 0
    prev_sign = None
    for (x0, y0), (x1, y1) in zip(samples, samples[1:]):
        if abs(x1 - x0) < 1e-9:
            continue
        slope = (y1 - y0) / (x1 - x0)
        slopes.append(slope)
        sign = 1 if slope >= 0 else -1
        if prev_sign is not None and sign != prev_sign:
            folds += 1
        prev_sign = sign
    abs_response = [abs(y) for _x, y in samples]
    return {
        "eps": eps,
        "folds": folds,
        "slope_min": min(slopes),
        "slope_max": max(slopes),
        "median_abs_response": sorted(abs_response)[len(abs_response) // 2],
        "max_abs_response": max(abs_response),
    }


def hgt_transfer_test() -> Dict[str, object]:
    eps_values = [0.02, 0.05, 0.10, 0.20, 0.50, 1.00, 1.50]
    return {"rows": [response_curve(eps) for eps in eps_values]}


def step12_followup(hgt: Dict[str, object]) -> Dict[str, object]:
    first_fold = None
    for row in hgt["rows"]:
        if row["folds"] > 0 and first_fold is None:
            first_fold = row["eps"]
    small_rows = [row for row in hgt["rows"] if row["eps"] <= 0.10]
    large_rows = [row for row in hgt["rows"] if row["eps"] >= 1.0]
    return {
        "first_fold_eps": first_fold,
        "small_max_response": max(row["max_abs_response"] for row in small_rows),
        "large_min_response": min(row["median_abs_response"] for row in large_rows),
    }


def main() -> None:
    node = node_prc_test()
    choice = transfer_choice()
    hgt = hgt_transfer_test()
    follow = step12_followup(hgt)

    print("R36 WELD_RESPONSE_REGIME")
    print("NODE_RESULT")
    for eps, min_deriv, fold in node["rows"]:
        print(f"  eps={eps:.2f} min_derivative={min_deriv:.3f} fold_regime={fold}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    for row in hgt["rows"]:
        print(
            f"  eps={row['eps']:.2f} folds={row['folds']} "
            f"slope_range=({row['slope_min']:.6g},{row['slope_max']:.6g}) "
            f"median_abs={row['median_abs_response']:.6g} max_abs={row['max_abs_response']:.6g}"
        )

    print("STEP9_METHOD_RESULT")
    print("  method=3 reverse it")
    print("  reversal=infer morphism class from response regime, not perturbation size as one scalar parameter")

    print("STEP12_FOLLOWUP")
    for key, value in follow.items():
        print(f"  {key}={value}")

    print("INTERPRETATION")
    print(
        "  The weld category needs a response-regime passport: small prime-phase perturbations "
        "and large reset-like perturbations are not the same morphism class. A scalar epsilon "
        "bound is weaker than reporting fold-free versus fold-forming carrier response."
    )


if __name__ == "__main__":
    main()
