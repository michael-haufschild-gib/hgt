#!/usr/bin/env python3
"""Extreme-height challenge for the apparent 6/gamma relative mismatch law."""

from __future__ import annotations

import argparse
import json
import os
from concurrent.futures import ProcessPoolExecutor

from contact_common import direct_period_integral


def evaluate(task):
    gamma, V, order = task
    pos = direct_period_integral(2j * gamma, V, order)
    neg = direct_period_integral(-2j * gamma, V, order)
    relative = abs(pos-neg) / max(abs(pos)+abs(neg), 1e-300)
    return {"gamma": gamma, "V": V, "order": order,
            "relative": float(relative), "gamma_relative": float(gamma*relative),
            "abs_signed": float(abs(pos-neg)),
            "conjugacy_error": float(abs(neg-pos.conjugate()) /
                                      max(abs(pos)+abs(neg), 1e-300))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--out", default="asymptotic.json")
    args = ap.parse_args()
    tasks = [(gamma, V, order)
             for gamma in (200.0, 300.0, 400.0, 500.0)
             for V in (2.0, 4.0, 8.0)
             for order in (80, 128)]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(evaluate, tasks, chunksize=1))
    payload = {"rows": rows,
               "max_order_change": max(abs(a["gamma_relative"]-b["gamma_relative"])
                 for a in rows for b in rows
                 if a["gamma"] == b["gamma"] and a["V"] == b["V"] and
                    a["order"] == 80 and b["order"] == 128)}
    tmp = args.out + ".tmp"
    with open(tmp, "w") as f:
        json.dump(payload, f, indent=2)
    os.replace(tmp, args.out)


if __name__ == "__main__":
    main()
