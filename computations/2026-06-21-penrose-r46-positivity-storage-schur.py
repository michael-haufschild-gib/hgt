#!/usr/bin/env python3
"""R46 candidate: mobile/immobile storage passport for positivity apex.

ResearchNode 12: Positivity apex (Conjecture B).

NODE: time-dependent exchange between mobile fracture flow and immobile matrix
storage.

Transfer: low-degree / visible positivity can be a mobile-block certificate
only.  A hidden storage block coupled through an exchange term can carry a
negative Schur complement even when the mobile and storage blocks are each
positive in isolation.
"""

from __future__ import annotations

import math
from statistics import median

import numpy as np


NODE = "time-dependent exchange between mobile fracture flow and immobile matrix storage"


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_exchange_test() -> None:
    dt = 0.01
    ts = np.arange(0.0, 30.0 + dt, dt)
    mobile = np.zeros_like(ts)
    storage = np.zeros_like(ts)
    outflow = np.zeros_like(ts)
    mobile[0] = 1.0
    for i in range(1, len(ts)):
        t = ts[i - 1]
        k_in = 0.45 * math.exp(-t / 12.0)
        k_out = 0.035 / (1.0 + t) ** 0.35
        advect = 0.22
        dm = -advect * mobile[i - 1] - k_in * mobile[i - 1] + k_out * storage[i - 1]
        ds = k_in * mobile[i - 1] - k_out * storage[i - 1]
        mobile[i] = max(0.0, mobile[i - 1] + dt * dm)
        storage[i] = max(0.0, storage[i - 1] + dt * ds)
        outflow[i] = advect * mobile[i]

    early = (ts >= 1.0) & (ts <= 7.0)
    late = (ts >= 14.0) & (ts <= 30.0)
    slope, intercept = np.polyfit(ts[early], np.log(outflow[early] + 1e-300), 1)
    predicted_late = np.exp(intercept + slope * ts[late])
    tail_ratio = float(np.mean(outflow[late] / (predicted_late + 1e-300)))

    print("NODE mobile/immobile exchange test")
    print(f"early_exponential_rate={-slope:.6f}")
    print(f"late_tail_mean_ratio_vs_early_fit={tail_ratio:.3f}")
    print(f"final_mobile={mobile[-1]:.6e} final_storage={storage[-1]:.6e}")
    print(
        "NODE verdict: a mobile-only exponential fit misses delayed release "
        "from immobile storage."
    )


def inertia(a: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int, float]:
    eig = np.linalg.eigvalsh((a + a.T) / 2.0)
    return (
        int(np.sum(eig < -tol)),
        int(np.sum(np.abs(eig) <= tol)),
        int(np.sum(eig > tol)),
        float(np.min(eig)),
    )


def trial(rng: np.random.Generator, aligned: bool) -> dict[str, float]:
    obs_diag = np.linspace(0.20, 1.00, 6) * rng.uniform(0.96, 1.04, 6)
    store_diag = np.array([0.080, 0.125, 0.180]) * rng.uniform(0.96, 1.04, 3)
    a = np.diag(obs_diag)
    c = np.diag(store_diag)
    b = np.zeros((6, 3))
    strength = rng.uniform(0.137, 0.145)
    if aligned:
        b[0, 0] = strength
    else:
        b[-1, -1] = strength
    h = np.block([[a, b], [b.T, c]])
    schur = c - b.T @ np.linalg.inv(a) @ b
    ai = inertia(a)
    ci = inertia(c)
    hi = inertia(h)
    si = inertia(schur)
    return {
        "a_neg": ai[0],
        "c_neg": ci[0],
        "h_neg": hi[0],
        "s_neg": si[0],
        "a_min": ai[3],
        "c_min": ci[3],
        "h_min": hi[3],
        "s_min": si[3],
    }


def transfer_audit() -> None:
    attempts = [
        "positivity apex needs an immobile-storage Schur-complement passport",
        "low-degree hankel positivity can miss delayed storage exchange",
        "change positivity certificate into mobile storage block form",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #17: change representation")
    print("represent certificate as block form H=[[A,B],[B^T,C]]")
    print("A=observed/mobile positivity, C=storage positivity, Schur=C-B^T A^-1 B")

    rng = np.random.default_rng(4612)
    aligned = [trial(rng, aligned=True) for _ in range(80)]
    control = [trial(rng, aligned=False) for _ in range(80)]

    def count(rows: list[dict[str, float]], key: str) -> int:
        return sum(1 for row in rows if row[key] > 0)

    print()
    print("HGT transfer: hidden storage Schur-complement audit")
    print("family A_positive C_positive Schur_negative full_negative median_A_min median_C_min median_Schur_min median_full_min")
    for label, rows in [("aligned_exchange", aligned), ("stiff_control", control)]:
        a_pos = sum(1 for row in rows if row["a_neg"] == 0)
        c_pos = sum(1 for row in rows if row["c_neg"] == 0)
        print(
            f"{label:16s} {a_pos:02d}/80 {c_pos:02d}/80 "
            f"{count(rows, 's_neg'):02d}/80 {count(rows, 'h_neg'):02d}/80 "
            f"{median(row['a_min'] for row in rows):+.6f} "
            f"{median(row['c_min'] for row in rows):+.6f} "
            f"{median(row['s_min'] for row in rows):+.6f} "
            f"{median(row['h_min'] for row in rows):+.6f}"
        )
    print(
        "passport_rule=do not promote finite/visible positivity until the "
        "hidden-storage Schur complement is bounded positive"
    )


def main() -> None:
    print("Penrose R46: storage-exchange Schur passport for positivity apex")
    print(f"NODE: {NODE}")
    node_exchange_test()
    transfer_audit()


if __name__ == "__main__":
    main()
