#!/usr/bin/env python3
import importlib.util
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "2026-06-21-penrose-r27-step11-period-boundary-stress.py"
spec = importlib.util.spec_from_file_location("r27step11", SRC)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def summarize_group(field, ns, delta):
    zeros = [float(mp.im(mp.zetazero(n))) for n in ns]
    mats = [mod.sample_matrix(field, z0, delta=delta) for z0 in zeros]
    avg = sum(mats) / len(mats)
    avg_min = float(np.linalg.eigvalsh(avg)[0])
    mins = [float(np.linalg.eigvalsh(m)[0]) for m in mats]
    return avg_min, float(np.mean(mins)), float(np.min(mins)), avg_min - float(np.mean(mins))


if __name__ == "__main__":
    print("STEP 12 battery: D_infty two-lane period-boundary stress")
    print("pass rules: xi boundary > finite/random by >=0.15; xi annealed gap <=0.005; off-line strong lowers xi boundary by >=0.08.")
    groups = {
        "early": [20, 21, 22, 23],
        "mid": [60, 61, 62, 63],
        "late": [120, 121, 122, 123],
    }
    deltas = [0.10, 0.14, 0.20]
    total = 0
    pass_sep = 0
    pass_gap = 0
    pass_offline = 0
    for gname, ns in groups.items():
        for delta in deltas:
            xi = summarize_group("xi", ns, delta)
            finite = summarize_group("finite_gamma", ns, delta)
            random = summarize_group("random_gamma", ns, delta)
            offline = summarize_group("xi_offline_strong", ns, delta)
            sep = xi[1] - max(finite[1], random[1])
            offline_drop = xi[1] - offline[1]
            ok_sep = sep >= 0.15
            ok_gap = abs(xi[3]) <= 0.005
            ok_offline = offline_drop >= 0.08
            total += 1
            pass_sep += int(ok_sep)
            pass_gap += int(ok_gap)
            pass_offline += int(ok_offline)
            print(
                f"group={gname} delta={delta:.2f} "
                f"xi_q={xi[1]:.6f} xi_gap={xi[3]:.6f} "
                f"finite_q={finite[1]:.6f} random_q={random[1]:.6f} "
                f"offline_q={offline[1]:.6f} sep={sep:.6f} offdrop={offline_drop:.6f} "
                f"ok_sep={int(ok_sep)} ok_gap={int(ok_gap)} ok_offline={int(ok_offline)}"
            )
    print(f"SUMMARY total={total} pass_sep={pass_sep} pass_gap={pass_gap} pass_offline={pass_offline}")
