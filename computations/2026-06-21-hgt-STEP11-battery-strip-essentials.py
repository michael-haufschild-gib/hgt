#!/usr/bin/env python3
"""THE-MACHINE Step 11 for battery temperature/SOC metaphor.

Method #7:
    Strip it to essentials. The battery NODE has two essential moving pieces:
    a changed calibration curve and a changed hysteresis/history gain. This
    script ablates each piece and asks whether the HT signal still survives.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


BASE = Path(__file__).with_name("2026-06-21-hgt-STEP8-battery-temperature-ht-calibration.py")
spec = importlib.util.spec_from_file_location("battery_ht", BASE)
battery_ht = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(battery_ht)


def error_with_mode(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], mode: str, seed: int) -> float:
    rng_ref = np.random.default_rng(seed)
    rng_target = np.random.default_rng(seed + 1)
    ref = battery_ht.lane(kind, 0.5, window, samples, primes, rng_ref)
    target = battery_ht.lane(kind, sigma, window, samples, primes, rng_target)
    ref_gain = 0.03 + 0.45 * float(np.median(ref["defect"]))
    target_gain = 0.03 + 0.45 * float(np.median(target["defect"]))
    ref_tau = 10.0 + 28.0 * float(np.mean(ref["defect"] > 0.0))
    target_tau = 10.0 + 28.0 * float(np.mean(target["defect"] > 0.0))
    v_ref, h_ref, amp_lo, amp_hi = battery_ht.make_trace(ref, None, None, ref_gain, ref_tau)

    if mode == "full":
        data = target
        gain = target_gain
        tau = target_tau
    elif mode == "amplitude_only":
        data = target
        gain = 0.0
        tau = target_tau
    elif mode == "history_only":
        data = {"amp": ref["amp"], "defect": target["defect"]}
        gain = target_gain
        tau = target_tau
    elif mode == "shuffle_defect":
        shuffled = target["defect"].copy()
        rng_target.shuffle(shuffled)
        data = {"amp": target["amp"], "defect": shuffled}
        gain = target_gain
        tau = target_tau
    elif mode == "reference_everything":
        data = {"amp": ref["amp"], "defect": target["defect"]}
        gain = ref_gain
        tau = ref_tau
    else:
        raise ValueError(mode)
    v, hidden, _, _ = battery_ht.make_trace(data, amp_lo, amp_hi, gain, tau)
    pred = battery_ht.estimate_hidden(v_ref, h_ref, v)
    return float(np.median(np.abs(pred - hidden)))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=120)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    primes = battery_ht.first_primes(args.prime_count)
    modes = ["full", "amplitude_only", "history_only", "shuffle_defect", "reference_everything"]
    cases = [
        ("true", 0.3, (100.0, 170.0)),
        ("true", 0.3, (500.0, 570.0)),
        ("true", 1.2, (100.0, 170.0)),
        ("finite", 0.3, (100.0, 170.0)),
        ("finite", 1.2, (100.0, 170.0)),
        ("random-phase", 0.3, (100.0, 170.0)),
        ("random-phase", 1.2, (100.0, 170.0)),
    ]
    print("STEP11 method #7: strip temperature-calibration metaphor to essentials")
    print("kind sigma window mode median_abs_hidden_error")
    for case_index, (kind, sigma, window) in enumerate(cases):
        for mode in modes:
            err = error_with_mode(kind, sigma, window, args.samples, primes, mode, seed=20260621 + 31 * case_index)
            print(f"{kind:13s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {mode:20s} {err:.6f}")
    print(
        "\nInterpretation key: if amplitude-only, shuffled-defect, or right-strip "
        "controls reproduce the full error, then the metaphor has been stripped "
        "to an ordinary calibration artifact rather than a new HT constraint."
    )


if __name__ == "__main__":
    main()
