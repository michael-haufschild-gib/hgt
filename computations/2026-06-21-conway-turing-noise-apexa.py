#!/usr/bin/env python3
"""THE-MACHINE tick: Turing initial-noise spectrum -> APEX-A.

NODE:
  Initial noise spectrum matters because early mode competition amplifies only
  perturbations overlapping unstable eigenmodes.

Consolidated target:
  APEX-A -- Schanuel-for-prime-logs / algebraic independence.

STEP 9 method:
  6. Ask what action is happening.
"""

from __future__ import annotations

import itertools
import math

import numpy as np


NODE = (
    "initial noise spectrum matters because early mode competition amplifies only "
    "perturbations overlapping unstable eigenmodes"
)

TRANSFER_ATTEMPTS = [
    "initial spectrum of relation search decides which APEX A monomial modes can be seen",
    "Schanuel finite test is unstable mode projection not scalar precision",
    "APEX A dependence can be invisible when coefficient noise misses the relation support",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606213821)
    modes = np.arange(1, 65)
    k0 = 14
    growth = 0.22 - 0.0065 * (modes - k0) ** 2
    unstable = growth > 0
    time = 22.0
    spectra: dict[str, np.ndarray] = {}
    spectra["white"] = np.abs(rng.normal(size=len(modes)))
    spectra["lowpass_misses"] = np.where(modes <= 6, np.abs(rng.normal(size=len(modes))), 0.0)
    spectra["notch_unstable"] = np.where(~unstable, np.abs(rng.normal(size=len(modes))), 0.0)
    spectra["targeted_unstable"] = np.exp(-0.5 * ((modes - k0) / 2.0) ** 2)
    spectra["highpass_weak"] = np.where(modes >= 28, np.abs(rng.normal(size=len(modes))), 0.0)

    lines = ["STEP 6 NODE TEST: Turing mode competition is projection plus amplification"]
    lines.append(
        "The linear operator has a fixed unstable band. Different initial spectra are evolved "
        "by exp(lambda_k t); only spectra with overlap in the unstable band form the selected pattern."
    )
    lines.append("spectrum unstable_overlap final_unstable_fraction final_amp dominant_mode dominant_growth")
    for name, amp0 in spectra.items():
        final = amp0 * np.exp(growth * time)
        overlap = float(np.linalg.norm(amp0[unstable]) / (np.linalg.norm(amp0) + 1e-300))
        final_frac = float(np.linalg.norm(final[unstable]) / (np.linalg.norm(final) + 1e-300))
        dom = int(modes[int(np.argmax(final))])
        dom_growth = float(growth[modes == dom][0])
        lines.append(
            f"{name:17s} {overlap:.6f} {final_frac:.6f} {float(np.linalg.norm(final)):.6e} "
            f"{dom:02d} {dom_growth:+.6f}"
        )
    lines.append(
        "NODE verdict: the operator's unstable modes are not enough. Pattern formation also "
        "requires initial spectral overlap; lowpass/notched spectra miss the instability even "
        "though the instability exists."
    )
    return lines


def monomial_basis(xs: np.ndarray) -> tuple[list[str], np.ndarray, dict[str, int]]:
    names = ["1"]
    values = [1.0]
    for i, x in enumerate(xs):
        names.append(f"L{i}")
        values.append(float(x))
    for i in range(len(xs)):
        for j in range(i, len(xs)):
            names.append(f"L{i}L{j}")
            values.append(float(xs[i] * xs[j]))
    return names, np.array(values), {name: i for i, name in enumerate(names)}


def random_coefficients(
    rng: np.random.Generator,
    dim: int,
    height: int,
    count: int,
    allowed: list[int] | None = None,
) -> np.ndarray:
    allowed = list(range(dim)) if allowed is None else allowed
    coeffs = np.zeros((count, dim), dtype=int)
    for row in range(count):
        vals = rng.integers(-height, height + 1, size=len(allowed))
        if np.all(vals == 0):
            vals[0] = 1
        coeffs[row, allowed] = vals
    return coeffs


def sparse_random_coefficients(
    rng: np.random.Generator,
    dim: int,
    height: int,
    count: int,
    support_size: int,
) -> np.ndarray:
    coeffs = np.zeros((count, dim), dtype=int)
    for row in range(count):
        support = rng.choice(dim, size=support_size, replace=False)
        vals = rng.integers(-height, height + 1, size=support_size)
        if np.all(vals == 0):
            vals[0] = 1
        coeffs[row, support] = vals
    return coeffs


def scan(name: str, coeffs: np.ndarray, values: np.ndarray, relation: np.ndarray) -> tuple[str, float, int, float]:
    residuals = np.abs(coeffs @ values)
    norms = np.linalg.norm(coeffs, axis=1) * np.linalg.norm(values)
    normalized = residuals / (norms + 1e-300)
    overlaps = np.abs(coeffs @ relation) / ((np.linalg.norm(coeffs, axis=1) + 1e-300) * np.linalg.norm(relation))
    hits = int(np.sum(residuals < 1e-12))
    return name, float(np.min(normalized)), hits, float(np.max(overlaps))


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Turing linear-stability formulas do not apply unchanged to APEX-A. The minimal transfer "
        "keeps the action: project onto candidate modes, then amplify/detect. Here the modes are "
        "degree-<=2 prime-log monomials and candidate integer relation supports."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 6: ASK WHAT ACTION IS HAPPENING")
    lines.append(
        "Action: finite relation experiments are not passive precision tests. They choose an "
        "initial coefficient spectrum, project it onto possible relation supports, then amplify "
        "small residuals. Missing the support is analogous to missing the unstable Turing mode."
    )

    rng = np.random.default_rng(2606213907)
    primes = np.array([2, 3, 5, 7, 11], dtype=float)
    actual_logs = np.log(primes)
    planted_logs = actual_logs.copy()
    planted_logs[4] = actual_logs[0] * actual_logs[1]
    names, planted_values, index = monomial_basis(planted_logs)
    _, actual_values, _ = monomial_basis(actual_logs)

    relation = np.zeros(len(names), dtype=int)
    relation[index["L0L1"]] = 1
    relation[index["L4"]] = -1
    degree1 = [idx for idx, name in enumerate(names) if "L" not in name or ("L" in name and "L" not in name[1:])]
    omit_cross = [idx for idx, name in enumerate(names) if name != "L0L1"]

    targeted = []
    for a, b in itertools.product(range(-3, 4), repeat=2):
        c = np.zeros(len(names), dtype=int)
        c[index["L0L1"]] = a
        c[index["L4"]] = b
        if np.any(c):
            targeted.append(c)
    targeted_coeffs = np.array(targeted, dtype=int)

    strategies = [
        ("degree1_only", random_coefficients(rng, len(names), 6, 6000, degree1)),
        ("cross_mode_omitted", random_coefficients(rng, len(names), 6, 6000, omit_cross)),
        ("sparse2_random", sparse_random_coefficients(rng, len(names), 6, 10000, 2)),
        ("dense_random", random_coefficients(rng, len(names), 3, 10000)),
        ("support_targeted", targeted_coeffs),
    ]
    lines.append(
        "strategy planted_min_norm_resid planted_hits planted_max_relation_overlap "
        "actual_min_norm_resid actual_hits actual_max_relation_overlap"
    )
    for name, coeffs in strategies:
        p_name, p_min, p_hits, p_overlap = scan(name, coeffs, planted_values, relation)
        _, a_min, a_hits, a_overlap = scan(name, coeffs, actual_values, relation)
        lines.append(
            f"{p_name:18s} {p_min:.3e} {p_hits:05d} {p_overlap:.4f} "
            f"{a_min:.3e} {a_hits:05d} {a_overlap:.4f}"
        )
    relation_resid_actual = float(abs(relation @ actual_values))
    relation_resid_planted = float(abs(relation @ planted_values))
    lines.append(
        f"planted_relation_residual={relation_resid_planted:.3e} "
        f"same_vector_on_actual_logs_residual={relation_resid_actual:.6e}"
    )
    lines.append(
        "\nProvisional interpretation: finite APEX-A searches must report coefficient-spectrum "
        "coverage. A negative result from degree-1, omitted-cross, sparse-random, or dense-random "
        "probes can miss even a planted degree-2 relation; targeted support finds it. On actual "
        "prime logs the same vector is nonzero, as expected."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: Turing initial-noise spectrum -> APEX-A")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 18/32 APEX-A Schanuel-for-prime-logs")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
