"""Run ONLY on the authorized Runpod host. No output may be used in a Lean proof."""
import os
for variable in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[variable] = "1"

import concurrent.futures as futures
import json
import time
from pathlib import Path
import numpy as np
from scipy.special import roots_legendre

A = 0.25
LAMBDAS = (1.75, 2.0, 3.0, 5.0)
CENTERS = np.arange(161) / 80
FREQUENCIES = np.arange(193) / 4
WORKERS = min(12, os.cpu_count() or 1)


def log_source_and_slope(y, atoms):
    y = np.abs(np.asarray(y))
    q1 = np.pi * np.exp(2 * y)
    q = q1[..., None] * np.arange(1, atoms + 1) ** 2
    relative = np.exp(-(q - q1[..., None]))
    values = np.sum((4*q*q - 6*q) * relative, axis=-1)
    derivatives = np.sum((-8*q**3 + 30*q*q - 15*q) * relative, axis=-1)
    slope = np.where(y == 0, 0, derivatives / values)
    return y/2 - q1 + np.log(values), slope


def row(task):
    index, nodes, atoms = task
    x = CENTERS[index]
    u, w = roots_legendre(nodes)
    t = 2 * (u + 1)
    w = 2 * w
    lx, slope = log_source_and_slope(x, atoms)
    plus, _ = log_source_and_slope(x+t, atoms)
    minus, _ = log_source_and_slope(x-t, atoms)
    p = np.exp(plus + minus - 2*lx)
    values = 2 * (np.cos(2*FREQUENCIES[:, None]*t) @ (w*p))
    return index, values, float(slope)


def grid(pool, nodes, atoms):
    out = np.empty((len(CENTERS), len(FREQUENCIES)))
    slopes = np.empty(len(CENTERS))
    for index, values, slope in pool.map(row, [(i, nodes, atoms) for i in range(len(CENTERS))]):
        out[index] = values
        slopes[index] = slope
    return out, slopes


def coefficients(lam, slopes):
    x = CENTERS
    acoth = np.ones_like(x)
    acoth[1:] = 2*A*x[1:] / np.tanh(2*A*x[1:])
    return np.exp(-2*lam*x) * (2 + acoth + 2*x*slopes - 2*lam*x)


def mp_point(task):
    import mpmath as mp
    xi, bi, digits, atoms = task
    mp.mp.dps = digits
    x, b = mp.mpf(xi)/80, mp.mpf(bi)/4

    def logs(y):
        y = abs(y)
        q1 = mp.pi*mp.exp(2*y)
        qs = [q1*n*n for n in range(1, atoms+1)]
        rel = [mp.exp(-(q-q1)) for q in qs]
        total = mp.fsum((4*q*q-6*q)*r for q,r in zip(qs,rel))
        slope = mp.fsum((-8*q**3+30*q*q-15*q)*r for q,r in zip(qs,rel))/total
        return y/2-q1+mp.log(total), (mp.mpf(0) if y == 0 else slope)

    lx, slope = logs(x)
    def integrand(t):
        lp, _ = logs(x+t)
        lm, _ = logs(x-t)
        return 2*mp.exp(lp+lm-2*lx)*mp.cos(2*b*t)
    breaks = [mp.mpf(k)/4 for k in range(17)]
    w = mp.quad(integrand, breaks)
    hs = {}
    for lam in LAMBDAS:
        lam = mp.mpf(str(lam))
        h = mp.mpf(3) if x == 0 else mp.exp(-2*lam*x)*(2+(x/2)*mp.coth(x/2)+2*x*slope-2*lam*x)
        hs[str(float(lam))] = mp.nstr(h, digits)
    return {"center_index": xi, "frequency_index": bi, "digits": digits, "atoms": atoms,
            "W": mp.nstr(w, digits), "h": hs}


def main():
    start = time.monotonic()
    result = {"aperture": A, "lambdas": LAMBDAS, "workers": WORKERS,
              "center_count": len(CENTERS), "frequency_count": len(FREQUENCIES)}
    with futures.ProcessPoolExecutor(max_workers=WORKERS) as pool:
        low, slopes_low = grid(pool, 512, 7)
        high, slopes_high = grid(pool, 1024, 14)
        discrepancy = float(np.max(np.abs(high-low)))
        threshold = max(1e-12, 100*discrepancy)
        result.update(max_grid_discrepancy=discrepancy, provisional_threshold=threshold)
        selected = []
        confirmations = set()
        for lam in LAMBDAS:
            h = coefficients(lam, slopes_high)
            positive, negative = np.where(h > 1e-10)[0], np.where(h < -1e-10)[0]
            lower = -high[positive]/h[positive, None]
            upper = -high[negative]/h[negative, None]
            ip = positive[np.argmax(lower, axis=0)]
            im = negative[np.argmin(upper, axis=0)]
            columns = np.arange(len(FREQUENCIES))
            margins = (h[ip]*high[im,columns]-h[im]*high[ip,columns])/(h[ip]-h[im])
            bi = int(np.argmin(margins))
            pi, ni = int(ip[bi]), int(im[bi])
            record = {"lambda": lam, "frequency_index": bi, "b": float(FREQUENCIES[bi]),
                      "positive_center_index": pi, "negative_center_index": ni,
                      "x_positive": float(CENTERS[pi]), "x_negative": float(CENTERS[ni]),
                      "W_positive": float(high[pi,bi]), "W_negative": float(high[ni,bi]),
                      "h_positive": float(h[pi]), "h_negative": float(h[ni]),
                      "margin": float(margins[bi]), "provisional_conflict": bool(margins[bi] < -threshold)}
            selected.append(record)
            if record["provisional_conflict"]:
                for xi in (pi, ni):
                    for digits, atoms in ((60,10),(90,18)):
                        confirmations.add((xi,bi,digits,atoms))
        result["selected"] = selected
        result["grid_seconds"] = time.monotonic()-start
        Path("grid.json").write_text(json.dumps(result, indent=2)+"\n")
        print(json.dumps({"grid_seconds": result["grid_seconds"], "selected": selected}), flush=True)
        checks = list(pool.map(mp_point, sorted(confirmations)))
        result["high_precision_points"] = checks
    import mpmath as mp
    mp.mp.dps = 90
    checked_margins = []
    for record in result["selected"]:
        if not record["provisional_conflict"]:
            continue
        for digits in (60,90):
            def lookup(xi):
                return next(p for p in checks if p["center_index"] == xi and
                            p["frequency_index"] == record["frequency_index"] and p["digits"] == digits)
            pp, pn = lookup(record["positive_center_index"]), lookup(record["negative_center_index"])
            key = str(record["lambda"])
            hp, hn = mp.mpf(pp["h"][key]), mp.mpf(pn["h"][key])
            wp, wn = mp.mpf(pp["W"]), mp.mpf(pn["W"])
            margin = (hp*wn-hn*wp)/(hp-hn)
            checked_margins.append({"lambda": record["lambda"], "digits": digits,
                                    "margin": mp.nstr(margin,digits)})
    result["checked_margins"] = checked_margins
    result["elapsed_seconds"] = time.monotonic()-start
    Path("results.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"elapsed_seconds": result["elapsed_seconds"], "checked_margins": checked_margins}), flush=True)


if __name__ == "__main__":
    main()
