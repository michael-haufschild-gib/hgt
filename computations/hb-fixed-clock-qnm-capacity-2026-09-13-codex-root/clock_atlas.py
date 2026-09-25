import json
import math
import multiprocessing as mpool
import os
import time

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import mpmath as mp
import numpy as np


ORDER = 320
OVERTONES = tuple(range(9))
LGRID = np.linspace(0.05, 3.0, 1201)
CHANNELS = (
    ("branch1_side1", 2.5, -3.0),
    ("branch1_side0", 1.5, -2.0),
    ("branch0_side1", -1.5, -1.0),
    ("branch0_side0", -2.5, 0.0),
)


def quadrature(order):
    x, w = np.polynomial.legendre.leggauss(order)
    u = 0.25 * (x + 1.0)
    weights = 0.25 * w
    logq = -1.0 / u + 1.0 / (1.0 - u)
    q = np.exp(logq)
    dchi = q / (1.0 + q) ** 2 * (u ** -2 + (1.0 - u) ** -2)
    return u - 0.5, 2.0 * weights * dchi


X, W = quadrature(ORDER)


def centered_transform_many(zs):
    zs = np.asarray(zs, dtype=np.complex128)
    return np.cosh(zs[:, None] * X[None, :]).dot(W)


def coherence_many(zs):
    zs = np.asarray(zs, dtype=np.complex128)
    num = np.abs(centered_transform_many(zs))
    den = np.real(centered_transform_many(zs.real.astype(np.complex128)))
    return num / den


def analyze_height(item):
    label, beta, gamma, kind = item
    rho = beta + 1j * gamma
    modes = []
    values = []
    for cname, a, b in CHANNELS:
        for n in OVERTONES:
            z = a * rho + b + 2.0 * n
            c = coherence_many(LGRID * z)
            modes.append({"channel": cname, "n": n, "z": [z.real, z.imag]})
            values.append(c)
    C = np.vstack(values).T
    worst = C.max(axis=1)
    rms = np.sqrt(np.mean(C * C, axis=1))
    iw = int(np.argmin(worst))
    ir = int(np.argmin(rms))
    isingle_flat = int(np.argmin(C))
    il, imode = np.unravel_index(isingle_flat, C.shape)
    unit = np.array([coherence_many(np.array([m["z"][0] + 1j * m["z"][1]]))[0] for m in modes])
    return {
        "label": label,
        "kind": kind,
        "beta": beta,
        "gamma": gamma,
        "mode_count": len(modes),
        "best_worst": {
            "L": float(LGRID[iw]),
            "coherence": float(worst[iw]),
            "rms": float(rms[iw]),
            "count_below_1e-6": int(np.sum(C[iw] < 1e-6)),
            "count_below_1e-3": int(np.sum(C[iw] < 1e-3)),
        },
        "best_rms": {
            "L": float(LGRID[ir]),
            "coherence": float(rms[ir]),
            "worst": float(worst[ir]),
            "count_below_1e-6": int(np.sum(C[ir] < 1e-6)),
            "count_below_1e-3": int(np.sum(C[ir] < 1e-3)),
        },
        "strongest_single": {
            "L": float(LGRID[il]),
            "coherence": float(C[il, imode]),
            **modes[imode],
        },
        "unit_duration": {
            "min": float(unit.min()),
            "median": float(np.median(unit)),
            "max": float(unit.max()),
            "count_below_1e-6": int(np.sum(unit < 1e-6)),
            "count_below_1e-3": int(np.sum(unit < 1e-3)),
        },
    }


def mp_chi(u):
    if u <= 0:
        return mp.mpf("0")
    if u >= 1:
        return mp.mpf("1")
    a = mp.exp(-1 / u)
    b = mp.exp(-1 / (1 - u))
    return a / (a + b)


def mp_dchi(u):
    if u <= 0 or u >= 1:
        return mp.mpf("0")
    a = mp.exp(-1 / u)
    b = mp.exp(-1 / (1 - u))
    return a * b * (u ** -2 + (1 - u) ** -2) / (a + b) ** 2


def mp_integrate_piecewise(fun):
    cuts = [mp.mpf(k) / 32 for k in range(33)]
    return mp.fsum(mp.quad(fun, [cuts[k], cuts[k + 1]]) for k in range(32))


def validate_candidate(cand):
    z = mp.mpc(cand["z"][0], cand["z"][1]) * mp.mpf(cand["L"])
    out = {}
    for dps in (80, 120):
        mp.mp.dps = dps
        direct = mp.e ** (-z / 2) * mp_integrate_piecewise(lambda u: mp_dchi(u) * mp.e ** (z * u))
        ibp = mp.e ** (-z / 2) * (1 - z * mp_integrate_piecewise(lambda u: (mp_chi(u) - 1) * mp.e ** (z * u)))
        den = mp.e ** (-mp.re(z) / 2) * mp_integrate_piecewise(
            lambda u: mp_dchi(u) * mp.e ** (mp.re(z) * u)
        )
        out[str(dps)] = {
            "direct_re": mp.nstr(mp.re(direct), 35),
            "direct_im": mp.nstr(mp.im(direct), 35),
            "coherence": mp.nstr(abs(direct) / den, 35),
            "direct_ibp_abs_error": mp.nstr(abs(direct - ibp), 12),
        }
    return out


def main():
    started = time.time()
    mp.mp.dps = 40
    zeros = [float(mp.im(mp.zetazero(k))) for k in range(1, 11)]
    items = [(f"zeta{k+1}", 0.5, g, "zeta") for k, g in enumerate(zeros)]
    items += [(f"mid{k+1}", 0.5, (zeros[k] + zeros[k + 1]) / 2, "midpoint") for k in range(9)]
    for k in (0, 3, 9):
        items.append((f"tilt_low_zeta{k+1}", 0.2, zeros[k], "tilt"))
        items.append((f"tilt_high_zeta{k+1}", 0.8, zeros[k], "tilt"))
    with mpool.Pool(processes=min(16, len(items))) as pool:
        rows = pool.map(analyze_height, items)
    candidates = []
    for r in rows:
        candidate = dict(r["strongest_single"])
        candidate.update({"height_label": r["label"], "beta": r["beta"], "gamma": r["gamma"]})
        candidates.append(candidate)
    best = min(candidates, key=lambda x: x["coherence"])
    validation = validate_candidate(best)
    summary = {}
    for kind in ("zeta", "midpoint", "tilt"):
        rr = [r for r in rows if r["kind"] == kind]
        summary[kind] = {
            "median_best_worst": float(np.median([r["best_worst"]["coherence"] for r in rr])),
            "min_best_worst": float(min(r["best_worst"]["coherence"] for r in rr)),
            "median_best_rms": float(np.median([r["best_rms"]["coherence"] for r in rr])),
            "min_single": float(min(r["strongest_single"]["coherence"] for r in rr)),
        }
    payload = {
        "formula": "centered literal smoothTransition derivative transform",
        "quadrature_order": ORDER,
        "overtone_range": [min(OVERTONES), max(OVERTONES)],
        "duration_grid": [float(LGRID[0]), float(LGRID[-1]), len(LGRID)],
        "rows": rows,
        "summary": summary,
        "strongest_single_validation": {"candidate": best, "precision": validation},
        "seconds": time.time() - started,
    }
    with open("clock-atlas.json", "w") as f:
        json.dump(payload, f, indent=2)


if __name__ == "__main__":
    main()
