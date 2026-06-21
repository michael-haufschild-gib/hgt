#!/usr/bin/env python3
"""
R36: BZ induction/exposure -> construction-obligation induction passport.

NODE side: oxygen exposure changes induction time and amplitude. If the
induction period is excluded, exposure can be hidden by a steady oscillation fit.

HGT side: a carrier construction fitted only on a steady/high window can hide
finite-source conditioning errors that appear in early/near-source windows.
"""

import math
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


def rmse(xs: Sequence[float], ys: Sequence[float]) -> float:
    return math.sqrt(sum((x - y) ** 2 for x, y in zip(xs, ys)) / len(xs))


def node_bz_induction_test() -> Dict[str, object]:
    times = [0.1 * k for k in range(600)]

    def trace(exposure: float) -> List[float]:
        tau = 6.0 + 5.0 * exposure
        amp = 1.0 - 0.25 * exposure
        out = []
        for t in times:
            gate = 1.0 / (1.0 + math.exp(-(t - tau) / 0.9))
            out.append(gate * amp * math.sin(2 * math.pi * (t - tau) / 8.0))
        return out

    low = trace(0.0)
    high = trace(1.0)
    post = [i for i, t in enumerate(times) if t >= 18.0]
    induction = [i for i, t in enumerate(times) if 4.0 <= t <= 14.0]
    # Best post-induction amplitude rescale for high exposure.
    num = sum(low[i] * high[i] for i in post)
    den = sum(high[i] * high[i] for i in post)
    scale = num / den
    high_scaled = [scale * y for y in high]
    return {
        "post_rmse_after_scale": rmse([low[i] for i in post], [high_scaled[i] for i in post]),
        "induction_rmse_after_scale": rmse([low[i] for i in induction], [high_scaled[i] for i in induction]),
        "scale": scale,
        "low_first_halfmax_time": next(t for t, y in zip(times, low) if abs(y) > 0.45),
        "high_first_halfmax_time": next(t for t, y in zip(times, high) if abs(y) > 0.45),
    }


def primes_upto(n: int) -> List[int]:
    out = []
    for k in range(2, n + 1):
        ok = True
        for p in out:
            if p * p > k:
                break
            if k % p == 0:
                ok = False
                break
        if ok:
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


def carrier_delta(s: complex, finite: bool = False, pmax: int = 47) -> float:
    A = A_term(s)
    P = P_finite(s, pmax) if finite else P_true(s)
    return max(math.log(max(abs(A), 1e-300)), math.log(max(abs(P), 1e-300))) - math.log(max(abs(A + P), 1e-300))


def fit_affine(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float]:
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    vx = sum((x - mx) ** 2 for x in xs)
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    a = cov / vx if vx > 0 else 0.0
    b = my - a * mx
    return a, b


def transfer_choice() -> Dict[str, object]:
    base = """
for oscillator trace:
    fit after induction can hide exposure
test: include induction window and post-induction window separately
"""
    attempts = {
        "A_construction_induction_passport": """
for carrier construction:
    fit finite source model on steady window
test: early/source window residual exposes missing induction passport
""",
        "B_steady_carrier_fit_only": """
for carrier construction:
    fit finite source model on high t window only
test: steady fit certifies construction
""",
        "C_pole_window_only": """
for carrier construction:
    test only near pole/Gamma source window
test: pole residual certifies construction
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    return {"distances": distances, "chosen": min(distances, key=distances.get)}


def hgt_transfer_test() -> Dict[str, object]:
    sigma = 0.5
    steady_ts = [30.0 + 0.25 * k for k in range(33)]
    early_ts = [14.0 + 0.25 * k for k in range(33)]
    true_steady = [carrier_delta(complex(sigma, t), finite=False) for t in steady_ts]
    fin_steady = [carrier_delta(complex(sigma, t), finite=True, pmax=47) for t in steady_ts]
    true_early = [carrier_delta(complex(sigma, t), finite=False) for t in early_ts]
    fin_early = [carrier_delta(complex(sigma, t), finite=True, pmax=47) for t in early_ts]
    a, b = fit_affine(fin_steady, true_steady)
    fin_steady_fit = [a * x + b for x in fin_steady]
    fin_early_fit = [a * x + b for x in fin_early]
    return {
        "affine_fit_a_b": (a, b),
        "steady_rmse": rmse(true_steady, fin_steady_fit),
        "early_rmse": rmse(true_early, fin_early_fit),
        "steady_true_range": (min(true_steady), max(true_steady)),
        "early_true_range": (min(true_early), max(true_early)),
    }


def step12_followup() -> Dict[str, object]:
    rows = []
    for pmax in [11, 23, 47, 97]:
        sigma = 0.5
        steady_ts = [30.0 + 0.25 * k for k in range(33)]
        early_ts = [14.0 + 0.25 * k for k in range(33)]
        true_steady = [carrier_delta(complex(sigma, t), finite=False) for t in steady_ts]
        fin_steady = [carrier_delta(complex(sigma, t), finite=True, pmax=pmax) for t in steady_ts]
        true_early = [carrier_delta(complex(sigma, t), finite=False) for t in early_ts]
        fin_early = [carrier_delta(complex(sigma, t), finite=True, pmax=pmax) for t in early_ts]
        a, b = fit_affine(fin_steady, true_steady)
        rows.append((pmax, rmse(true_steady, [a * x + b for x in fin_steady]), rmse(true_early, [a * x + b for x in fin_early])))
    return {"rows": rows}


def main() -> None:
    node = node_bz_induction_test()
    choice = transfer_choice()
    hgt = hgt_transfer_test()
    follow = step12_followup()

    print("R36 CONSTRUCTION_INDUCTION_PASSPORT")
    print("NODE_RESULT")
    for key, value in node.items():
        print(f"  {key}={value}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    for key, value in hgt.items():
        print(f"  {key}={value}")

    print("STEP9_METHOD_RESULT")
    print("  method=4 change the viewpoint")
    print("  viewpoint_change=steady carrier fit -> induction/source-window passport")

    print("STEP12_FOLLOWUP")
    for pmax, steady, early in follow["rows"]:
        print(f"  pmax={pmax} steady_rmse={steady:.9g} early_rmse={early:.9g} ratio={early/max(steady,1e-300):.6g}")

    print("INTERPRETATION")
    print(
        "  A construction can look acceptable after excluding induction/conditioning windows. "
        "The source-built object needs an induction/source-window passport: fit on a steady "
        "carrier region must be checked against early/pole-like source windows."
    )


if __name__ == "__main__":
    main()
