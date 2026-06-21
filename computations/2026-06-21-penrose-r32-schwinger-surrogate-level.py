#!/usr/bin/env python3
"""
R32: Schwinger level quantization -> surrogate-ladder central-level gate.

NODE side: local commutator samples can look close while the fitted central
level is non-integral or regulator-unstable.

HGT side: an FE-even nonvanishing factor exp(c*(s-1/2)^2/2) preserves zeros
and the functional equation, but adds c*(s-1/2) to xi'/xi. Small c can be
nearly invisible to local phase-carrier statistics on finite windows while a
scale/level gate sees a stable nonzero coefficient.
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


def node_schwinger_test() -> Dict[str, object]:
    rng = random.Random(32015)
    modes = list(range(1, 13))
    true_k = 3.0
    fake_k = 3.08
    noise = [rng.uniform(-0.035, 0.035) for _ in modes]
    true_samples = [true_k * m + noise[i] for i, m in enumerate(modes)]
    fake_samples = [fake_k * m + noise[i] for i, m in enumerate(modes)]

    def fit_level(samples: Sequence[float]) -> float:
        num = sum(m * y for m, y in zip(modes, samples))
        den = sum(m * m for m in modes)
        return num / den

    def rmse(samples: Sequence[float], k: float) -> float:
        return math.sqrt(sum((y - k * m) ** 2 for m, y in zip(modes, samples)) / len(modes))

    kt = fit_level(true_samples)
    kf = fit_level(fake_samples)
    return {
        "true_level_fit": kt,
        "fake_level_fit": kf,
        "true_integer_residue": abs(kt - round(kt)),
        "fake_integer_residue": abs(kf - round(kf)),
        "true_local_rmse": rmse(true_samples, kt),
        "fake_local_rmse": rmse(fake_samples, kf),
        "fake_vs_true_local_rmse": rmse(fake_samples, true_k),
    }


def zeta_log_derivative(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(mp.diff(lambda w: mp.zeta(w), z) / mp.zeta(z))


def A_term(s: complex) -> complex:
    z = mp.mpc(s)
    return complex(1 / z + 1 / (z - 1) - mp.log(mp.pi) / 2 + mp.digamma(z / 2) / 2)


def H_true(s: complex) -> complex:
    return A_term(s) + zeta_log_derivative(s)


def delta_from_AH(s: complex, H: complex) -> float:
    A = A_term(s)
    P = H - A
    return max(math.log(max(abs(A), 1e-300)), math.log(max(abs(P), 1e-300))) - math.log(max(abs(H), 1e-300))


def sample_points(t0: float, t1: float, n_t: int = 28) -> List[complex]:
    sigmas = [0.30, 0.40, 0.50, 0.60, 0.70]
    ts = [t0 + (t1 - t0) * k / (n_t - 1) for k in range(n_t)]
    return [complex(sigma, t) for sigma in sigmas for t in ts]


def transfer_choice() -> Dict[str, object]:
    base = """
for modes m:
    commutator_sample[m] = k*m + noise
fit k over modes
test: local residual small but integer/level gate rejects wrong k
"""
    attempts = {
        "A_FE_even_nonvanishing_level_fake": """
for points s:
    H_fake = H_true + c*(s-1/2)
fit c over scale windows
test: FE and zeros preserved; carrier local gap small; stable level gate rejects c != 0
""",
        "B_finite_euler_cutoff_level": """
for prime cutoff N:
    estimate carrier gap against true H
fit N-dependent drift
test: cutoff drift distinguishes finite Euler from true analytic continuation
""",
        "C_random_phase_integer_snap": """
for random phase surrogates:
    estimate contour charge and snap to nearest integer
test: random phases fail integer contour charge stability
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    return {"distances": distances, "chosen": min(distances, key=distances.get)}


def hgt_surrogate_test() -> Dict[str, object]:
    points = sample_points(18.0, 24.0)
    windows = [(18.0, 24.0), (24.0, 30.0), (30.0, 36.0)]
    cs = [0.0, 1e-4, 5e-4, 1e-3, 5e-3]
    rows = []
    for c in cs:
        delta_gaps = []
        fe_resids = []
        level_estimates = []
        for s in points:
            h = H_true(s)
            hf = h + c * (s - 0.5)
            sm = 1 - s
            hm = H_true(sm)
            hfm = hm + c * (sm - 0.5)
            delta_gaps.append(abs(delta_from_AH(s, hf) - delta_from_AH(s, h)))
            fe_resids.append(abs(hf + hfm) / max(abs(hf) + abs(hfm), 1e-300))
            if abs(s - 0.5) > 1e-12:
                level_estimates.append(((hf - h) / (s - 0.5)).real)
        rows.append(
            (
                c,
                median(delta_gaps),
                max(delta_gaps),
                median(fe_resids),
                max(fe_resids),
                median(level_estimates),
            )
        )

    stability = []
    c = 1e-3
    for t0, t1 in windows:
        pts = sample_points(t0, t1)
        estimates = []
        for s in pts:
            h = H_true(s)
            hf = h + c * (s - 0.5)
            estimates.append(((hf - h) / (s - 0.5)).real)
        stability.append((t0, t1, median(estimates), max(estimates) - min(estimates)))

    return {"rows": rows, "stability": stability}


def step12_followup() -> Dict[str, object]:
    tolerances = [1e-2, 5e-3, 1e-3, 5e-4]
    rows = hgt_surrogate_test()["rows"]
    return {
        "threshold_rows": [
            (row[0], tol, row[1] < tol, row[2] < tol)
            for row in rows
            if row[0] > 0
            for tol in tolerances
        ],
        "nearby_false": "FE-exact and zero-preserving do not imply carrier-equivalent",
        "minimal_counterexample": "nonvanishing FE-even exponential factor with c != 0",
    }


def apply_method_14_weaken_conjecture(hgt: Dict[str, object]) -> Dict[str, object]:
    row = next(row for row in hgt["rows"] if abs(row[0] - 1e-3) < 1e-12)
    return {
        "method": "14 weaken the conjecture",
        "weakened_claim": "finite local carrier tests are vulnerable to FE-even zero-preserving level fakes",
        "c": row[0],
        "median_delta_gap": row[1],
        "median_level_estimate": row[5],
    }


def main() -> None:
    node = node_schwinger_test()
    choice = transfer_choice()
    hgt = hgt_surrogate_test()
    method = apply_method_14_weaken_conjecture(hgt)
    follow = step12_followup()

    print("R32 SCHWINGER_SURROGATE_LEVEL")
    print("NODE_RESULT")
    for key, value in node.items():
        print(f"  {key}={value}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    print("  c median_delta_gap max_delta_gap median_FE_residual max_FE_residual median_level_estimate")
    for row in hgt["rows"]:
        print(
            f"  c={row[0]:.5g} median_delta_gap={row[1]:.9g} max_delta_gap={row[2]:.9g} "
            f"median_FE_residual={row[3]:.3e} max_FE_residual={row[4]:.3e} level={row[5]:.9g}"
        )
    print("  stability_windows c=0.001")
    for t0, t1, med, spread in hgt["stability"]:
        print(f"  window={t0:.1f}-{t1:.1f} median_level={med:.9g} spread={spread:.3e}")

    print("STEP9_METHOD_RESULT")
    for key, value in method.items():
        print(f"  {key}={value}")

    print("STEP12_FOLLOWUP")
    for c, tol, median_pass, max_pass in follow["threshold_rows"]:
        print(f"  c={c:.1e} tol={tol:.1e} median_delta_pass={median_pass} max_delta_pass={max_pass}")
    print(f"  nearby_false={follow['nearby_false']}")
    print(f"  minimal_counterexample={follow['minimal_counterexample']}")

    print("INTERPRETATION")
    print(
        "  FE-exact, zero-preserving nonvanishing factors form an epsilon-ladder for local carrier "
        "statistics: small c can pass finite median-delta tolerances while carrying a stable nonzero "
        "level coefficient. Surrogate ladders need a scale-stable level/growth gate, not only FE and "
        "correct-zero checks."
    )


if __name__ == "__main__":
    main()
