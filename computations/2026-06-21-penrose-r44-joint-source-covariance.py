#!/usr/bin/env python3
"""R44 candidate: joint-source covariance passport for source-built kappa_-.

NODE: transcriptional activity changes local stiffness, compaction, and
motor-driven motion simultaneously.

Transfer: a source-built faithful index should not be certified by one-source
or pairwise source sweeps alone.  The construction must audit the joint source
cone, because co-varying source channels can create a negative square while
all coordinate and pairwise checks remain positive.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from statistics import median

import numpy as np


NODE = (
    "transcriptional activity changes local stiffness compaction and "
    "motor-driven motion simultaneously"
)


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def inertia(a: np.ndarray, tol: float = 1e-9) -> tuple[int, int, int, float]:
    eig = np.linalg.eigvalsh((a + a.T) / 2.0)
    return (
        int(np.sum(eig < -tol)),
        int(np.sum(np.abs(eig) <= tol)),
        int(np.sum(eig > tol)),
        float(np.min(eig)),
    )


def node_test() -> None:
    """Small linearized polymer model with three simultaneous drivers."""
    jac = np.array(
        [
            [-1.80, 0.65, -0.30],
            [0.20, 1.35, 0.10],
            [-0.75, -0.25, 1.55],
        ],
        dtype=float,
    )
    true_delta = np.array([0.34, -0.28, 0.52], dtype=float)
    observed = jac @ true_delta
    joint_fit, *_ = np.linalg.lstsq(jac, observed, rcond=None)

    print("NODE simultaneous-driver test")
    print("driver order: stiffness compaction motor")
    print(
        "true_delta="
        f"{true_delta[0]:+.3f},{true_delta[1]:+.3f},{true_delta[2]:+.3f} "
        "joint_fit="
        f"{joint_fit[0]:+.3f},{joint_fit[1]:+.3f},{joint_fit[2]:+.3f}"
    )
    print("one_axis_fit axis_delta residual_norm")
    for axis, name in enumerate(["stiffness", "compaction", "motor"]):
        col = jac[:, axis]
        fit = float(col @ observed / (col @ col))
        residual = float(np.linalg.norm(observed - fit * col))
        print(f"{name:10s} {fit:+.3f} {residual:.6f}")
    print(
        "NODE verdict: one-driver fits explain the same observations badly; "
        "the constraint is simultaneous identifiability."
    )


@dataclass
class Trial:
    axis_positive: bool
    pair_positive: bool
    joint_negative: bool
    axis_min: float
    pair_min: float
    joint_min: float


def source_trial(rng: np.random.Generator, aligned: bool, n: int = 12) -> Trial:
    base = np.diag(np.r_[0.08, np.linspace(0.18, 1.40, n - 1)])
    shared = np.zeros(n)
    shared[0] = 1.0
    channels = []
    for _ in range(3):
        if aligned:
            v = 0.99 * shared + 0.015 * rng.normal(size=n)
        else:
            v = rng.normal(size=n)
        v = v / np.linalg.norm(v)
        channels.append(-0.030 * np.outer(v, v) + 0.001 * np.eye(n))

    axis = [inertia(base + channel) for channel in channels]
    pairs = [
        inertia(base + channels[i] + channels[j])
        for i, j in itertools.combinations(range(3), 2)
    ]
    joint = inertia(base + sum(channels))
    return Trial(
        axis_positive=all(row[0] == 0 for row in axis),
        pair_positive=all(row[0] == 0 for row in pairs),
        joint_negative=joint[0] > 0,
        axis_min=min(row[3] for row in axis),
        pair_min=min(row[3] for row in pairs),
        joint_min=joint[3],
    )


def transfer_audit() -> None:
    attempts = [
        "source-built kappa needs a joint-source perturbation passport",
        "kappa axis tests miss simultaneous Euler Gamma FE drift",
        "split source construction identifiability and inertia certification",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #1: split it into subclaims")
    print("subclaim A: source-channel construction")
    print("subclaim B: joint-channel identifiability over the co-variation cone")
    print("subclaim C: faithful signed-form inertia certificate")

    rng = np.random.default_rng(44012)
    aligned = [source_trial(rng, aligned=True) for _ in range(80)]
    control = [source_trial(rng, aligned=False) for _ in range(80)]

    def count(rows: list[Trial], pred) -> int:
        return sum(1 for row in rows if pred(row))

    aligned_miss = count(
        aligned,
        lambda row: row.axis_positive and row.pair_positive and row.joint_negative,
    )
    control_miss = count(
        control,
        lambda row: row.axis_positive and row.pair_positive and row.joint_negative,
    )

    print()
    print("HGT transfer: faithful signed forms with three source channels")
    print("family trials axis_positive pair_positive joint_negative axis_pair_miss")
    print(
        "aligned "
        f"{count(aligned, lambda row: row.axis_positive):02d}/80 "
        f"{count(aligned, lambda row: row.pair_positive):02d}/80 "
        f"{count(aligned, lambda row: row.joint_negative):02d}/80 "
        f"{aligned_miss:02d}/80"
    )
    print(
        "decorrelated "
        f"{count(control, lambda row: row.axis_positive):02d}/80 "
        f"{count(control, lambda row: row.pair_positive):02d}/80 "
        f"{count(control, lambda row: row.joint_negative):02d}/80 "
        f"{control_miss:02d}/80"
    )
    print(
        "aligned_medians "
        f"axis_min={median(row.axis_min for row in aligned):+.6f} "
        f"pair_min={median(row.pair_min for row in aligned):+.6f} "
        f"joint_min={median(row.joint_min for row in aligned):+.6f}"
    )
    print(
        "decorrelated_medians "
        f"axis_min={median(row.axis_min for row in control):+.6f} "
        f"pair_min={median(row.pair_min for row in control):+.6f} "
        f"joint_min={median(row.joint_min for row in control):+.6f}"
    )
    print(
        "passport_rule=coordinate and pairwise source sweeps are insufficient; "
        "certify the whole admissible joint-source cone before claiming kappa_-=0"
    )


def main() -> None:
    print("Penrose R44: joint-source covariance passport for source-built kappa_-")
    print(f"NODE: {NODE}")
    node_test()
    transfer_audit()


if __name__ == "__main__":
    main()
