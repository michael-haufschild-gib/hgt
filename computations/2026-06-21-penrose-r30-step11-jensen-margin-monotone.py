#!/usr/bin/env python3
import importlib.util
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "2026-06-21-penrose-r30-jensen-coupled-defect-transition.py"
spec = importlib.util.spec_from_file_location("r30", SRC)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def margin_field_window(nsites, t0, t1):
    ts = np.linspace(t0, t1, nsites)
    coeffs = np.array([mod.jensen3_coeffs(t) for t in ts])
    discs = []
    for row in coeffs:
        discs.append(mod.cubic_discriminant(row[3], row[2], row[1], row[0]))
    discs = np.asarray(discs, dtype=float)
    margins = np.log10(np.maximum(discs, 1e-300))
    margins = (margins - np.percentile(margins, 10)) / (np.percentile(margins, 90) - np.percentile(margins, 10) + 1e-12)
    margins = np.clip(margins, 0.0, 1.0)
    return ts, coeffs, margins


def one(window, nsites, eps, length):
    _, coeffs, margins = margin_field_window(nsites, window[0], window[1])
    true_c, true_d, true_p = mod.defect_count(coeffs, margins, eps, length, shuffle_margin=False)
    shuf_c, shuf_d, shuf_p = mod.defect_count(coeffs, margins, eps, length, shuffle_margin=True)
    sorted_m = np.sort(margins)
    sort_c, sort_d, sort_p = mod.defect_count(coeffs, sorted_m, eps, length, shuffle_margin=False)
    return true_c, true_d, true_p, shuf_c, shuf_d, shuf_p, sort_c, sort_d, sort_p


if __name__ == "__main__":
    print("STEP 11 method 13: monotone suppression ratio for Jensen TP defects")
    print("true/shuffled < 1 means the actual Jensen margin order suppresses collective defects.")
    windows = [(5.0, 80.0), (80.0, 155.0), (155.0, 230.0)]
    for nsites in [24, 48]:
        for eps in [0.9, 1.1, 1.3]:
            ratios = []
            for length in [0, 2, 5, 8]:
                row_ratios = []
                for window in windows:
                    true_c, true_d, true_p, shuf_c, shuf_d, shuf_p, sort_c, sort_d, sort_p = one(window, nsites, eps, length)
                    ratio = true_c / (shuf_c + 1e-9)
                    row_ratios.append(ratio)
                    print(
                        f"window={int(window[0])}-{int(window[1])} nsites={nsites} eps={eps:.1f} length={length} "
                        f"true_count={true_c:.3f} shuf_count={shuf_c:.3f} sorted_count={sort_c:.3f} "
                        f"ratio={ratio:.3f} true_domains={true_d:.3f} shuf_domains={shuf_d:.3f} sorted_domains={sort_d:.3f}"
                    )
                ratios.append(float(np.mean(row_ratios)))
            print(f"SUMMARY nsites={nsites} eps={eps:.1f} mean_ratio_by_length={','.join(f'{r:.3f}' for r in ratios)}")
