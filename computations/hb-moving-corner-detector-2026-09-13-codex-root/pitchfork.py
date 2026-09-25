import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

from experiment import observable

MODE = os.environ["PITCHFORK_MODE"]
DERIVATIVE = MODE == "full"
OUT = "pitchfork-" + MODE + ".jsonl"


def imag_ratio(sigma, height, L):
    return mp.im(observable(mp.mpc(sigma, height), L, DERIVATIVE)[1])


def central_data(height, L):
    slope = mp.diff(lambda x: imag_ratio(x, height, L), mp.mpf(".5"))
    cubic = mp.diff(lambda x: imag_ratio(x, height, L), mp.mpf(".5"), 3) / 6
    return slope, cubic


def roots_sigma(height, L):
    sigmas = [mp.mpf(".02") + i * mp.mpf(".96") / 96 for i in range(97)]
    vals = []
    for sigma in sigmas:
        W, ratio = observable(mp.mpc(sigma, height), L, DERIVATIVE)
        vals.append((sigma, mp.im(ratio), abs(W[1])))
    roots = []
    for (a, fa, da), (b, fb, db) in zip(vals, vals[1:]):
        if min(da, db) < mp.mpf("1e-45"):
            continue
        if fa == 0 or fa * fb < 0:
            try:
                root = mp.findroot(lambda x: imag_ratio(x, height, L), (a, b), tol=mp.mpf("1e-55"), maxsteps=50)
                if mp.mpf(".02") < root < mp.mpf(".98") and not any(abs(root - x) < mp.mpf("1e-30") for x in roots):
                    roots.append(root)
            except Exception:
                pass
    return roots


def classify_height(height_text):
    mp.mp.dps = 80
    height = mp.mpf(height_text)
    L0, L1 = 2 * mp.e, mp.mpf(40)
    grid = [L0 * mp.power(L1 / L0, mp.mpf(i) / 48) for i in range(49)]
    out = {"kind": "height", "mode": MODE, "height": height_text, "slope_grid": [], "bifurcations": [], "root_counts": []}
    try:
        slopes = []
        for L in grid:
            slope, cubic = central_data(height, L)
            slopes.append((L, slope, cubic))
            out["slope_grid"].append([mp.nstr(L, 30), mp.nstr(slope, 50), mp.nstr(cubic, 50)])
        for (a, fa, _), (b, fb, _) in zip(slopes, slopes[1:]):
            if fa == 0 or fa * fb < 0:
                try:
                    root = mp.findroot(lambda L: central_data(height, L)[0], (a, b), tol=mp.mpf("1e-55"), maxsteps=60)
                    slope, cubic = central_data(height, root)
                    if L0 < root < L1 and not any(abs(root - mp.mpf(x["L"])) < mp.mpf("1e-28") for x in out["bifurcations"]):
                        out["bifurcations"].append({"L": mp.nstr(root, 65), "slope": mp.nstr(slope, 60), "cubic": mp.nstr(cubic, 60)})
                except Exception:
                    pass
        for L in (L0, mp.mpf(6), mp.mpf(8), mp.mpf(10), mp.mpf(15), mp.mpf(20), mp.mpf(30), mp.mpf(40)):
            roots = roots_sigma(height, L)
            symmetry = max([abs(roots[i] + roots[-1-i] - 1) for i in range(len(roots) // 2)] or [mp.mpf(0)])
            out["root_counts"].append({"L": mp.nstr(L, 30), "count": len(roots),
                                       "roots": [mp.nstr(x, 55) for x in roots], "reflection_error": mp.nstr(symmetry, 40)})
    except Exception as exc:
        out["error"] = str(exc)[:350]
    return out


def validate(job):
    height, L = map(mp.mpf, job)
    out = {"kind": "validation", "mode": MODE, "height": str(height), "L": str(L), "precision": []}
    try:
        for dps in (100, 160):
            mp.mp.dps = dps
            root = mp.findroot(lambda x: central_data(height, x)[0], (L * mp.mpf(".9999"), L * mp.mpf("1.0001")),
                               tol=mp.power(10, -dps + 15), maxsteps=50)
            slope, cubic = central_data(height, root)
            out["precision"].append({"dps": dps, "L": mp.nstr(root, dps), "slope": mp.nstr(slope, dps), "cubic": mp.nstr(cubic, dps)})
    except Exception as exc:
        out["error"] = str(exc)[:350]
    return out


def emit(row):
    with open(OUT, "a") as f:
        f.write(json.dumps(row) + "\n")
    print(json.dumps({k: v for k, v in row.items() if k not in ("slope_grid", "precision")}), flush=True)


def main():
    started = time.monotonic()
    heights = ["14.134725141734693790457251983562470270784257115699", "20", "30", "50", "75", "100", "150", "200"]
    with cf.ProcessPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(classify_height, heights, chunksize=1))
        for row in rows:
            emit(row)
        jobs = [[r["height"], b["L"]] for r in rows for b in r.get("bifurcations", [])]
        for row in pool.map(validate, jobs, chunksize=1):
            emit(row)
    emit({"kind": "complete", "mode": MODE, "seconds": time.monotonic() - started,
          "bifurcation_count": sum(len(r.get("bifurcations", [])) for r in rows)})


if __name__ == "__main__":
    main()
