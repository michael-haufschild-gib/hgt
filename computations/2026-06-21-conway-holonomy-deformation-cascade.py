#!/usr/bin/env python3
"""Workflow pass: stop-order cascades -> holonomy deformation-stability gate."""

from __future__ import annotations

import importlib.util
import math
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-poincare-contour-root-gate.py")
spec = importlib.util.spec_from_file_location("root_gate", BASE)
root_gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(root_gate)


def node_stop_cascade(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)

    def simulate(clustered: bool) -> tuple[int, float, float]:
        price = 100.0
        if clustered:
            stops = rng.normal(99.65, 0.035, size=260)
        else:
            stops = rng.uniform(98.9, 99.9, size=260)
        stops.sort()
        triggered = np.zeros(len(stops), dtype=bool)
        max_step = 0.0
        for _ in range(120):
            shock = 0.015 + 0.03 * rng.random()
            newly = (~triggered) & (stops >= price - shock) & (stops < price)
            impact = 0.0028 * int(np.sum(newly))
            step = shock + impact
            max_step = max(max_step, step)
            price -= step
            triggered |= stops >= price
            if price < 98.5:
                break
        return int(np.sum(triggered)), float(100.0 - price), max_step

    print("NODE: stop-order clustering amplifies short-term price cascades")
    print("case mean_triggered mean_drop mean_max_step")
    for name, clustered in [("uniform", False), ("clustered", True)]:
        rows = [simulate(clustered) for _ in range(120)]
        print(
            f"{name:9s} {np.mean([r[0] for r in rows]):.1f} "
            f"{np.mean([r[1] for r in rows]):.3f} {np.mean([r[2] for r in rows]):.3f}"
        )


def contour_fingerprint(rect: tuple[float, float, float, float], n_edge: int = 180) -> dict[str, object]:
    pts = root_gate.boundary(rect, n_edge)
    vals = [complex(root_gate.xi(z)) for z in pts]
    scores = []
    sides = []
    for idx, (v0, v1) in enumerate(zip(vals, vals[1:])):
        a0 = math.atan2(v0.imag, v0.real)
        a1 = math.atan2(v1.imag, v1.real)
        phase = abs(root_gate.principal_angle(a1 - a0))
        logjump = abs(math.log(abs(v1) + 1e-300) - math.log(abs(v0) + 1e-300))
        scores.append(phase + 0.35 * logjump)
        sides.append(min(3, idx // n_edge))
    scores = np.asarray(scores)
    event = scores >= np.quantile(scores, 0.94)
    side = np.bincount(np.asarray(sides)[event], minlength=4).astype(float)
    side = side / max(1.0, side.sum())
    wind, max_jump, min_abs, _ = root_gate.winding_from_points(pts)
    return {
        "winding": wind,
        "event_share": side,
        "event_count": int(np.sum(event)),
        "max_score": float(np.max(scores)),
        "max_jump": max_jump,
        "min_abs": min_abs,
    }


def transfer_deformation() -> None:
    print()
    print("TRANSFER: ResearchNode #4/#5/#6 holonomy/cohomology deformation stability")
    print("method #23 classify boundary cases: contour shape readouts must not avalanche under small deformations at fixed winding")
    zero1 = 14.134725141734693790457251983562
    prev = None
    print("half_width winding event_count event_side_share L1_from_prev max_score min_abs_xi")
    for hw in [0.025, 0.035, 0.050, 0.075, 0.110, 0.160, 0.240, 0.340]:
        rect = (0.5 - hw, 0.5 + hw, zero1 - 0.11, zero1 + 0.11)
        fp = contour_fingerprint(rect)
        l1 = float(np.sum(np.abs(fp["event_share"] - prev))) if prev is not None else 0.0
        prev = fp["event_share"]
        share = ",".join(f"{x:.2f}" for x in fp["event_share"])
        print(
            f"{hw:.3f} {fp['winding']:+.3f} {fp['event_count']:03d} "
            f"[{share}] {l1:.3f} {fp['max_score']:.3f} {fp['min_abs']:.2e}"
        )


def main() -> None:
    node_stop_cascade()
    transfer_deformation()


if __name__ == "__main__":
    main()
