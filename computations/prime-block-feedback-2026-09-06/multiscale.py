"""Numerical diagnostics on the authorized pod; no proof certificates."""
import argparse
import json
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
WIDTHS = [1, 2, 4, 8, 16]


def levels(errors, masses):
    out = []
    prior = None
    for width in WIDTHS:
        c = errors.reshape(-1, width).sum(axis=1)
        m = masses.reshape(-1, width).sum(axis=1)
        a = c/np.sqrt(m)
        record = {"width": width, "groups": len(a), "mean": float(a.mean()),
                  "mean_square": float(np.mean(a*a)), "variance": float(a.var()),
                  "max_absolute": float(np.max(np.abs(a)))}
        if prior is not None:
            child_pair_mean_square = (prior*prior).reshape(-1, 2).mean(axis=1)
            record["mean_square_ratio"] = float(np.mean(a*a)/np.mean(prior*prior))
            record["noncontracting_merges"] = int(np.sum(a*a > child_pair_mean_square))
        out.append(record)
        prior = a
    return out


def analyze(rows, whole, low, high):
    rows = rows[(rows[:, 0] >= low) & (rows[:, 0] < high)]
    whole = whole[(whole[:, 0] >= low) & (whole[:, 0] < high)]
    assert len(rows) == 16*len(whole)
    masses = rows[:, 5]
    c = rows[:, 4]-masses
    actual = levels(c, masses)
    matrix = c.reshape(-1, 16)
    totals = masses.reshape(-1, 16).sum(axis=1)
    diagonal = float(np.mean(np.sum(matrix*matrix, axis=1)/totals))
    cross = [{"lag": lag, "contribution": float(np.mean(
        2*np.sum(matrix[:, :-lag]*matrix[:, lag:], axis=1)/totals))}
        for lag in range(1, 16)]
    reconstructed = diagonal + sum(row["contribution"] for row in cross)
    direct_whole_mse = float(np.mean(whole[:, 8]**2))
    assert abs(reconstructed-actual[-1]["mean_square"]) < 1e-12
    assert abs(direct_whole_mse-reconstructed) < 1e-9
    rng = np.random.default_rng(6060906+low)
    a = c/np.sqrt(masses)
    controls = np.array([[entry["mean_square"] for entry in
        levels(rng.permutation(a)*np.sqrt(masses), masses)] for _ in range(256)])
    return {"range": [low, high-1], "levels": actual,
        "diagonal_full_block": diagonal, "cross_terms_full_block": cross,
        "whole_block_check_absolute_error": abs(reconstructed-direct_whole_mse),
        "shuffle_mean_squares_quantiles": {
            str(w): {"q05": float(np.quantile(controls[:,j], .05)),
                     "q50": float(np.quantile(controls[:,j], .5)),
                     "q95": float(np.quantile(controls[:,j], .95))}
            for j,w in enumerate(WIDTHS)},
        "all_doublings_contract_20_percent": all(
            entry["mean_square_ratio"] <= .8 for entry in actual[1:])}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=["discovery", "validation"])
    args = parser.parse_args()
    start = time.monotonic()
    rows = np.load(ROOT/"rows-r16.npz")["rows"]
    whole = np.load(ROOT/"rows-r1.npz")["rows"]
    if args.phase == "discovery":
        rows, whole = rows[rows[:,0] < 32], whole[whole[:,0] < 32]
        intervals = [(4,24), (24,32)]
    else:
        gate = json.loads((ROOT/"multiscale-discovery.json").read_text())
        assert gate["advance"], "Do not spend the held-out data on a failed discovery candidate."
        intervals = [(32,64), (64,90)]
    results = [analyze(rows, whole, *bounds) for bounds in intervals]
    out = {"phase": args.phase, "candidate": "M1", "results": results,
           "advance": all(r["all_doublings_contract_20_percent"] for r in results),
           "wall_seconds": time.monotonic()-start}
    (ROOT/f"multiscale-{args.phase}.json").write_text(json.dumps(out, indent=2))
    print(json.dumps({"phase": args.phase, "advance": out["advance"],
        "ranges": [{"range": r["range"], "levels": r["levels"],
                    "diagonal": r["diagonal_full_block"],
                    "cross_terms": r["cross_terms_full_block"]} for r in results],
        "wall_seconds": out["wall_seconds"]}, indent=2))
