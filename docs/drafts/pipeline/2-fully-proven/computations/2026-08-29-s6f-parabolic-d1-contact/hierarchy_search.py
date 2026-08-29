#!/usr/bin/env python3
"""Hostile derivative-hierarchy test for parabolic D1.

Diagnostic only. No output is admissible in a Lean proof. Tests whether the
surviving strict clock-square concavity is the first sign of an alternating
finite derivative hierarchy or an isolated second-order fact.
"""

from __future__ import annotations

import concurrent.futures
import importlib.util
import json
import os
import sys
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "run_experiments.py"
spec = importlib.util.spec_from_file_location("contact", SCRIPT)
contact = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = contact
spec.loader.exec_module(contact)

PRISM: sp.Expr | None = None


def job(order: int) -> tuple[int, dict]:
    assert PRISM is not None
    # k=2 is known negative; the hoped-for hierarchy has sign (-1)^(k+1).
    corrected = (-1) ** (order + 1) * sp.diff(PRISM, contact.W, order)
    return order, contact.half_prism_record(corrected)


def main() -> None:
    print("reconstructing parabolic D1 prism", file=sys.stderr, flush=True)
    value = contact.normalized_value().subs(contact.core.V, contact.core.Z * contact.core.Y)
    contact.BASE = contact.even_z_to_w(sp.expand(value))
    global PRISM
    PRISM = contact.parabolic_prism()
    orders = list(range(2, 25))
    print("dispatching alternating clock derivatives", file=sys.stderr, flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=min(len(orders), os.cpu_count() or 1)) as pool:
        records = dict(pool.map(job, orders))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "sign_convention": "(-1)^(k+1) d^k D1/dw^k expected positive",
        "records": {str(k): records[k] for k in orders},
    }
    Path("hierarchy-results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    for order in orders:
        signs = records[order]["bernstein"]
        print(order, signs["negative"], signs["zero"], signs["positive"])


if __name__ == "__main__":
    main()
