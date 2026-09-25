#!/usr/bin/env python3
"""High-precision re-evaluation of apparent CLG curvature failures."""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("topology", HERE / "run_experiments.py")
TOPOLOGY = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = TOPOLOGY
SPEC.loader.exec_module(TOPOLOGY)

U = "1.8235194811474678"  # A approximately 120.5; higher atoms need > 160 digits.
TAUS = ("0.0002393041143881613", "0.001", "0.01", "0.1", "0.5", "1.0")


def evaluate(dps: int):
    TOPOLOGY.initialize(dps)
    u = mp.mpf(U)
    records = []
    for tau_text in TAUS:
        tau = mp.mpf(tau_text)
        t = u * tau
        atom = TOPOLOGY.BASE.atom_jets(u, t)
        full = TOPOLOGY.BASE.full_jets(u, t)
        likelihood = tuple(full[i] - atom[i] for i in range(7))
        for lam in (mp.mpf(0), mp.mpf(1)):
            extended = TOPOLOGY.at_lambda(atom, likelihood, t, lam)
            jets = tuple(atom[i] + lam * likelihood[i] for i in range(7))
            original = TOPOLOGY.BASE.margin_and_variations(jets, likelihood, t)
            assert mp.almosteq(extended[2], original[2])
            records.append({
                "tau": tau_text,
                "lambda": int(lam),
                "second": mp.nstr(extended[2], 80),
                "second_scale": mp.nstr(extended[4], 80),
                "normalized_second": mp.nstr(
                    extended[2] / extended[4] if extended[4] else extended[2], 80),
                "third": mp.nstr(extended[3], 80),
                "likelihood_max_abs": mp.nstr(max(map(abs, likelihood)), 80),
            })
    return records


result = {str(dps): evaluate(dps) for dps in (200, 400, 600)}
Path("witness-audit.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps(result, indent=2, sort_keys=True))
