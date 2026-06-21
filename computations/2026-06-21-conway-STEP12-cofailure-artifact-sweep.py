import importlib.util
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-cofailure-artifact-channel-gate.py")
spec = importlib.util.spec_from_file_location("gate", BASE)
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
frailty = gate.frailty


def add_artifact(reserve, count, width):
    n = reserve.shape[1]
    start = n // 3
    stop = min(n, start + width)
    rows = []
    for j in range(count):
        row = np.ones(n) * 0.95
        row[start + j : min(n, stop + j)] = 0.0
        rows.append(row)
    return np.vstack([reserve, np.asarray(rows)]), np.asarray(rows)


def main():
    print("STEP12 battery: co-failure artifact-channel sweep")
    primes = frailty.first_primes(100)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7]
    window = (100.0, 170.0)
    finite = frailty.lane_matrix("finite", sigmas, window, 140, primes, seed=20260658, mode="phase")
    true = frailty.lane_matrix("true", sigmas, window, 140, primes, seed=20260621, mode="phase")
    for thr in [0.12, 0.20]:
        base_true = frailty.metric(true, thr, 6100)
        base_finite = frailty.metric(finite, thr, 6101)
        print(f"THR {thr} true_exI={base_true['excess_indep']:+.3f} finite_exI={base_finite['excess_indep']:+.3f}")
        for count in [1, 2, 3, 5]:
            for width in [16, 40, 72]:
                mixed, arts = add_artifact(finite, count=count, width=width)
                m_mixed = frailty.metric(mixed, thr, 6200 + count * 10 + width)
                m_art = frailty.metric(arts, thr, 7200 + count * 10 + width)
                print(
                    f" count={count} width={width}",
                    f"mixed_exI={m_mixed['excess_indep']:+.3f}",
                    f"mixed_vis={m_mixed['visible']:.3f}",
                    f"art_only_exI={m_art['excess_indep']:+.3f}",
                    f"art_only_vis={m_art['visible']:.3f}",
                )


if __name__ == "__main__":
    main()
