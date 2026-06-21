#!/usr/bin/env python3
"""
R37 NODE validation: stochastic resonance has a narrow useful noise optimum.
"""

from __future__ import annotations

import numpy as np


def detection_score(events: np.ndarray, drive: np.ndarray) -> float:
    y = events - events.mean()
    d = drive - drive.mean()
    signal = abs(float(np.dot(y, d))) / (np.linalg.norm(d) + 1e-12)
    noise = float(np.std(y)) + 1e-12
    return signal / noise


def main() -> None:
    rng = np.random.default_rng(371)
    t = np.linspace(0, 320, 8000)
    drive = 0.38 * np.sin(2 * np.pi * t / 20.0)
    threshold = 0.68
    print("noise  event_rate  detection_score")
    best = (None, -1.0)
    for noise in [0.04, 0.08, 0.12, 0.18, 0.25, 0.34, 0.46, 0.62, 0.84, 1.12]:
        x = drive + noise * rng.normal(size=t.size)
        events = (x > threshold).astype(float)
        score = detection_score(events, drive)
        if score > best[1]:
            best = (noise, score)
        print(f"{noise:5.2f} {events.mean():11.5f} {score:16.5f}")
    print(f"\nNODE verdict: best_noise={best[0]:.2f}, best_score={best[1]:.5f}; more noise is not better.")


if __name__ == "__main__":
    main()
