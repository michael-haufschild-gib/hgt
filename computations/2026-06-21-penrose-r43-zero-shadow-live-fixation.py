#!/usr/bin/env python3
"""R43 candidate: live-window passport for zero-shadow topology.

NODE: fixed-cell artifacts can disagree with live-cell chromatin mobility.

Transfer: a zero-shadow bridge should not be accepted merely from a fixed
aggregate mask.  It needs a live-window persistence passport, and it must be
stable against a small "fixation smear" audit that can connect near-misses.
"""

from __future__ import annotations

import importlib.util
import pathlib
from statistics import median

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-thin-bridge-sampling.py")
spec = importlib.util.spec_from_file_location("thin_bridge", BASE)
thin_bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(thin_bridge)


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def time_dilate(mask: np.ndarray, radius: int) -> np.ndarray:
    """OR-neighborhood along the time axis, modeling fixation/time-smear."""
    out = mask.copy()
    for k in range(1, radius + 1):
        out[:, k:] |= mask[:, :-k]
        out[:, :-k] |= mask[:, k:]
    return out


def sliding_live_stats(mask: np.ndarray, width: int, stride: int) -> dict[str, float]:
    spans = []
    components = []
    largest = []
    occupied = []
    for lo in range(0, mask.shape[1] - width + 1, stride):
        st = thin_bridge.bridge_stats(mask[:, lo : lo + width])
        spans.append(st["span_t"])
        components.append(st["components"])
        largest.append(st["largest_frac"])
        occupied.append(st["occupied"])
    if not spans:
        return {
            "windows": 0.0,
            "span_rate": 0.0,
            "median_components": 0.0,
            "median_largest": 0.0,
            "median_occupied": 0.0,
        }
    return {
        "windows": float(len(spans)),
        "span_rate": float(np.mean(spans)),
        "median_components": float(median(components)),
        "median_largest": float(median(largest)),
        "median_occupied": float(median(occupied)),
    }


def node_fixed_vs_live() -> None:
    """Minimal moving-territory toy model: union spans, no live frame spans."""
    frames = []
    rows, cols = 35, 80
    for k in range(25):
        frame = np.zeros((rows, cols), dtype=bool)
        frame[8:27, 0:11] = True
        frame[8:27, 69:80] = True
        start = 10 + 2 * k
        frame[17:19, start : start + 12] = True
        frames.append(frame)

    live_spans = [thin_bridge.bridge_stats(frame)["span_t"] for frame in frames]
    live_components = [thin_bridge.bridge_stats(frame)["components"] for frame in frames]
    fixed_union = np.logical_or.reduce(frames)
    fixed = thin_bridge.bridge_stats(fixed_union)

    print("NODE fixed/live topology simulation")
    print(
        "live_frame_span_rate="
        f"{np.mean(live_spans):.3f} live_median_components={median(live_components):.0f} "
        f"fixed_union_components={fixed['components']:.0f} fixed_union_span_t={fixed['span_t']:.0f} "
        f"fixed_union_largest={fixed['largest_frac']:.3f}"
    )
    print("NODE validated: a fixed aggregate can create a connected bridge absent from every live frame.")


def transfer_audit() -> None:
    node = "differences between fixed-cell artifacts and live-cell chromatin mobility"
    attempts = [
        "zero-shadow topology needs a live-window persistence passport",
        "fixed zero-shadow aggregates may be fixation-smear bridges",
        "bridge geometry must survive live mobility rather than static union",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(node, item)):
        print(f"distance={levenshtein(node, text):3d}  {text}")

    print()
    print("STEP9 method #7: strip it to essentials")
    print("essentials: full fixed span, sliding live-window span, tiny time-smear span")

    primes = thin_bridge.first_primes(160)
    sigmas = np.linspace(0.2, 0.9, 17)
    windows = [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]
    thresholds = [0.85, 1.00]
    samples_t = 120

    true_persistent = 0
    true_rows = 0
    false_smear = 0
    artifact_rows = 0

    print()
    print("HGT transfer: zero-shadow live/fixation passport")
    print(
        "kind window threshold occupied full_comp full_span live45 live60 "
        "smear1_span smear3_span artifact_flag"
    )
    for window in windows:
        ts = np.linspace(window[0], window[1], samples_t)
        for threshold in thresholds:
            for kind in ["true", "finite", "random"]:
                seed = 730000 + int(window[0]) + int(100 * threshold) + {
                    "true": 1,
                    "finite": 2,
                    "random": 3,
                }[kind]
                rng = np.random.default_rng(seed)
                mask = thin_bridge.zero_shadow_mask(kind, sigmas, ts, primes, rng, threshold)
                full = thin_bridge.bridge_stats(mask)
                live45 = sliding_live_stats(mask, 45, 15)
                live60 = sliding_live_stats(mask, 60, 15)
                smear1 = thin_bridge.bridge_stats(time_dilate(mask, 1))
                smear3 = thin_bridge.bridge_stats(time_dilate(mask, 3))
                artifact = (
                    full["span_t"] == 0.0
                    and live45["span_rate"] == 0.0
                    and live60["span_rate"] == 0.0
                    and smear3["span_t"] == 1.0
                )
                if kind == "true":
                    true_rows += 1
                    if full["span_t"] == 1.0 and live45["span_rate"] >= 0.99 and live60["span_rate"] >= 0.99:
                        true_persistent += 1
                else:
                    artifact_rows += 1
                    if artifact:
                        false_smear += 1
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} "
                    f"{full['occupied']:.3f} {full['components']:.0f} {full['span_t']:.0f} "
                    f"{live45['span_rate']:.3f} {live60['span_rate']:.3f} "
                    f"{smear1['span_t']:.0f} {smear3['span_t']:.0f} {int(artifact)}"
                )

    print()
    print("Summary gates")
    print(f"true_persistent_rows={true_persistent}/{true_rows}")
    print(f"finite_random_fixation_artifacts={false_smear}/{artifact_rows}")
    print(
        "passport_rule=accept a zero-shadow bridge only when the fixed span is "
        "confirmed by live sliding-window spans and rejected as a mere time-smear bridge"
    )


def main() -> None:
    node_fixed_vs_live()
    transfer_audit()


if __name__ == "__main__":
    main()
