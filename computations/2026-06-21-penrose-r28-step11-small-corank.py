#!/usr/bin/env python3
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "2026-06-21-penrose-r28-ito-stratonovich-corank.py"
spec = importlib.util.spec_from_file_location("r28", SRC)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

if __name__ == "__main__":
    print("STEP 11 method 9: small finite-prime cases for Ito/Stratonovich rank correction")
    windows = [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]
    ns = [5, 10, 20, 30, 60, 100]
    for window in windows:
        for n in ns:
            vals = {}
            for kind in ["constant", "true", "finite", "random"]:
                ito, strat, stepdiff, maxdb = mod.ito_strato_dimension(kind, window, n=n)
                vals[kind] = strat - ito
            ctrl = max(abs(vals["finite"]), abs(vals["random"]))
            ratio = vals["true"] / (ctrl + 1e-9)
            print(
                f"window={int(window[0])}-{int(window[1])} n={n} "
                f"constant={vals['constant']:+.4f} true={vals['true']:+.4f} "
                f"finite={vals['finite']:+.4f} random={vals['random']:+.4f} "
                f"true_over_max_control={ratio:.2f}"
            )
