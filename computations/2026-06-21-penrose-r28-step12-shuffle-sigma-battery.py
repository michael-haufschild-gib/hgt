#!/usr/bin/env python3
import importlib.util
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "2026-06-21-penrose-r28-ito-stratonovich-corank.py"
spec = importlib.util.spec_from_file_location("r28", SRC)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def rank_delta_with_b(kind, window, sigma, n, shuffle=False):
    ts = np.linspace(window[0], window[1], 120)
    feat = mod.prime_feature_matrix(ts, sigma, n)
    dfeat = np.diff(feat, axis=0)
    b = mod.carrier_b(kind, ts, sigma, n=n, seed=int(window[0] + sigma * 1000))
    if shuffle:
        rng = np.random.default_rng(int(window[0] * 10 + sigma * 1000 + n))
        b = rng.permutation(b)
    ito = b[:-1, None] * dfeat
    strat = 0.5 * (b[:-1] + b[1:])[:, None] * dfeat
    return mod.effective_rank(strat) - mod.effective_rank(ito)


if __name__ == "__main__":
    print("STEP 12 battery: shuffle and sigma boundary cases for Ito/Stratonovich corank transfer")
    windows = [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]
    sigmas = [0.3, 0.5, 0.7, 1.2]
    n = 80
    pass_true = 0
    pass_shuffle = 0
    total = 0
    for window in windows:
        for sigma in sigmas:
            true = rank_delta_with_b("true", window, sigma, n, shuffle=False)
            true_shuf = rank_delta_with_b("true", window, sigma, n, shuffle=True)
            finite = rank_delta_with_b("finite", window, sigma, n, shuffle=False)
            random = rank_delta_with_b("random", window, sigma, n, shuffle=False)
            ctrl = max(abs(finite), abs(random))
            ok_true = true > ctrl + 0.50
            ok_shuffle = abs(true_shuf) < abs(true) * 0.65
            total += 1
            pass_true += int(ok_true)
            pass_shuffle += int(ok_shuffle)
            print(
                f"window={int(window[0])}-{int(window[1])} sigma={sigma:.1f} "
                f"true={true:+.4f} true_shuf={true_shuf:+.4f} "
                f"finite={finite:+.4f} random={random:+.4f} "
                f"ok_true={int(ok_true)} ok_shuffle={int(ok_shuffle)}"
            )
    print(f"SUMMARY total={total} pass_true={pass_true} pass_shuffle={pass_shuffle}")
