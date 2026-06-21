import importlib.util
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-q70-niche-conditioned-null.py")
spec = importlib.util.spec_from_file_location("q70_niche", BASE)
q70 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(q70)


def main():
    print("STEP12 battery: q-threshold niche-conditioned boundary cases")
    primes = q70.first_primes(120)
    sigmas = np.linspace(0.2, 0.9, 9)
    for q in [0.60, 0.70, 0.80, 0.90]:
        print(f"Q {q:.2f}")
        for kind in ["true", "finite", "random"]:
            excesses = []
            passes = 0
            for window in [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]:
                ts = np.linspace(window[0], window[1], 180)
                mat = q70.field(kind, sigmas, ts, primes, seed=5050 + int(window[0]) + len(kind) + int(q * 100))
                ev = q70.event_matrix(mat, q=q)
                raw = q70.top_eig(ev)
                mean, q95 = q70.time_count_null(ev, seed=6060 + int(window[0]) + len(kind) + int(q * 100), trials=180)
                excesses.append(raw - mean)
                passes += int(raw > q95)
            print(
                " ROW",
                kind,
                f"mean_excess={np.mean(excesses):+.5f}",
                f"min_excess={np.min(excesses):+.5f}",
                f"max_excess={np.max(excesses):+.5f}",
                f"above_q95={passes}/3",
            )


if __name__ == "__main__":
    main()
