#!/usr/bin/env python3
"""Intervention test for the three retained direct common-period components."""

from __future__ import annotations

import argparse
import json
import math
import os
import random
from concurrent.futures import ProcessPoolExecutor
from statistics import median

import mpmath as mp
import numpy as np

from contact_common import coefficients, clock_J_I10, integrate_gl, period_R


def zeta_zero(n):
    mp.mp.dps = 40
    return n, float(mp.im(mp.zetazero(n)))


def density_components(delta, h, V, order):
    _, _, _, c11, cjet, cq = coefficients(delta, h)
    period = period_R(delta, h, order)
    clock, i10 = clock_J_I10(V, h, order)
    return np.asarray((period * cq * clock,
                       period * cjet * clock,
                       -period * c11 * i10), dtype=np.complex128)


def component_integral(delta, V=4.0, order=80):
    gamma = abs(delta.imag) / 2
    h_order = max(order, int(order + 2.5 * gamma * V / math.pi))
    q0 = max(order, min(h_order, order + int(2.5 * gamma / math.pi)))
    out = integrate_gl(lambda h: density_components(delta, h, V, order),
                       0, min(1, V), q0)
    if V > 1:
        out += integrate_gl(lambda h: density_components(delta, h, V, order),
                            1, V, h_order)
    return out


def evaluate(task):
    kind, n, gamma, order = task
    pos = component_integral(2j * gamma, order=order)
    neg = component_integral(-2j * gamma, order=order)
    signed = pos - neg
    names = ("CQ_clock", "onset_jet", "lower_I10")
    full_pos, full_neg = sum(pos), sum(neg)
    row = {
        "kind": kind,
        "n": int(n),
        "gamma": float(gamma),
        "order": int(order),
        "full_relative": float(abs(full_pos-full_neg) /
                               max(abs(full_pos)+abs(full_neg), 1e-300)),
        "signed_internal_cancellation": float(abs(sum(signed)) /
                                              max(sum(abs(z) for z in signed), 1e-300)),
    }
    for j, name in enumerate(names):
        row[name + "_signed_abs"] = float(abs(signed[j]))
        keep = [k for k in range(3) if k != j]
        ap, am = sum(pos[k] for k in keep), sum(neg[k] for k in keep)
        row["without_" + name + "_relative"] = float(abs(ap-am) /
                                                        max(abs(ap)+abs(am), 1e-300))
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--zeros", type=int, default=64)
    ap.add_argument("--order", type=int, default=80)
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--out", default="components.json")
    args = ap.parse_args()
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        pairs = list(pool.map(zeta_zero, range(1, args.zeros + 1)))
    gs = [g for _, g in pairs]
    rng = random.Random(902171)
    tasks = [("actual", n, g, args.order) for n, g in pairs]
    for i, (n, g) in enumerate(pairs):
        left = g - (gs[i-1] if i else max(0, g-(gs[1]-g)))
        right = (gs[i+1] if i+1 < len(gs) else g+(g-gs[i-1])) - g
        tasks.append(("control", n, g+rng.uniform(-.45*left, .45*right), args.order))
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(evaluate, tasks, chunksize=1))
    summaries = {}
    metrics = ["full_relative", "signed_internal_cancellation",
               "without_CQ_clock_relative", "without_onset_jet_relative",
               "without_lower_I10_relative"]
    for kind in ("actual", "control"):
        selected = [r for r in rows if r["kind"] == kind]
        summaries[kind] = {key: median(r[key] for r in selected) for key in metrics}
    payload = {"rows": rows, "median": summaries,
               "actual_control_full_median_difference":
                   summaries["actual"]["full_relative"]-summaries["control"]["full_relative"]}
    tmp = args.out + ".tmp"
    with open(tmp, "w") as f:
        json.dump(payload, f, indent=2)
    os.replace(tmp, args.out)


if __name__ == "__main__":
    main()
