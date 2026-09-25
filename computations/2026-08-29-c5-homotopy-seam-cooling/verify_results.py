#!/usr/bin/env python3
"""Independent high-precision anchor verification for run_experiments.py."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import mpmath as mp


HERE = Path(__file__).parent
spec = importlib.util.spec_from_file_location("experiment", HERE / "run_experiments.py")
assert spec and spec.loader
experiment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(experiment)


def main() -> None:
    stored = json.loads((HERE / "results.json").read_text(encoding="utf-8"))
    assert stored["exact_symbolics"]["seam_factorization_verified"] is True
    old_dps, old_nmax = experiment.DPS, experiment.NMAX
    experiment.DPS, experiment.NMAX = 120, 20
    checks = []
    try:
        for a in (6, 10, 100, 1000):
            row = experiment.spectral_point(str(a))
            r2 = mp.mpf(row["R2_negF3_over_AF2"])
            r4 = mp.mpf(row["R4_negF5_over_AF4"])
            gap = mp.mpf(row["ratio_gap_2R2_minus_R4"])
            reserve = mp.mpf(row["fourth_cooling_reserve_F5_plus_6AF4"])
            seam = mp.mpf(row["source_seam_F2F5_minus_2F3F4"])
            assert r2 > 3
            assert r4 < 6
            assert gap > 0
            assert reserve > 0
            assert seam > 0
            checks.append({"A": a, "R2": str(r2), "R4": str(r4), "gap": str(gap)})
    finally:
        experiment.DPS, experiment.NMAX = old_dps, old_nmax
    print(json.dumps({"verified": True, "dps": 120, "nmax": 20, "checks": checks}, indent=2))


if __name__ == "__main__":
    main()
