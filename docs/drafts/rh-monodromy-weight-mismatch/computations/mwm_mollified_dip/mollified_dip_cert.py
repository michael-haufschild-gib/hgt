#!/usr/bin/env python3
"""
Doc 55 pre-registered certification: P1 (beta-profile linearity), P2 (mollified
value-distribution kernel), P3 (dip intervals). Predictions registered in
docs/drafts/rh-monodromy-weight-mismatch/55-mollified-dip.md BEFORE this run.

F_N(s) = sum_{n<=N} n^{-s};  M_y = sum_{d<=y} mu(d) d^{-s} (sharp) and
Barban-Vehov taper variant;  P = F_N * M_y = 1 + G.
Matched regime: T0 = 2*pi*(N+1/4)^2, window length U.
"""
import numpy as np, json, math, sys
from math import log, pi, sqrt
from multiprocessing import Pool

U = 2000.0
GRID = 0.01          # t-grid for P2 sampling and zero seeds
NLIST = [50, 100, 200, 400]
THETA = 0.5          # y = N^theta

def mu_sieve(y):
    mu = np.ones(y + 1, dtype=int)
    primes = []
    is_comp = np.zeros(y + 1, bool)
    for i in range(2, y + 1):
        if not is_comp[i]:
            primes.append(i); mu[i] = -1
        for p in primes:
            if i * p > y: break
            is_comp[i * p] = True
            mu[i * p] = 0 if i % p == 0 else -mu[i]
            if i % p == 0: break
    mu[0] = 0
    return mu

def mollifier(N, taper=False):
    y = int(round(N ** THETA))
    mu = mu_sieve(y)
    lam = mu.astype(float)
    if taper:
        y1 = max(2, int(round(sqrt(y))))
        for d in range(1, y + 1):
            if d <= y1: continue
            lam[d] *= log(y / d) / log(y / y1) if d < y else 0.0
    return y, lam

def conv_coeffs(N, y, lam):
    """coefficients of F_N * M_y on m = 1..N*y"""
    c = np.zeros(N * y + 1)
    for d in range(1, y + 1):
        if lam[d] == 0.0: continue
        c[d::d][:N] += lam[d]     # c[d*n] += lam[d], n = 1..N
    return c

def dirichlet_eval(vals, sigma, tgrid, chunk=4000):
    """sum_m vals[m] * m^{-sigma-it} for m>=1; vals is 1-indexed array."""
    m = np.nonzero(vals)[0]
    m = m[m >= 1]
    amp = vals[m] * m.astype(float) ** (-sigma)
    lg = np.log(m.astype(float))
    out = np.empty(len(tgrid), complex)
    for i in range(0, len(tgrid), chunk):
        tc = tgrid[i:i + chunk]
        out[i:i + chunk] = (amp[None, :] * np.exp(-1j * np.outer(tc, lg))).sum(1)
    return out

def F_and_dF(N, s_arr):
    """F_N and F_N' at complex points (vector)."""
    n = np.arange(1, N + 1, dtype=float)
    lg = np.log(n)
    E = np.exp(-np.outer(s_arr, lg))       # n^{-s}
    return E.sum(1), -(E * lg[None, :]).sum(1)

def newton_zeros(N, T0, sig_seed, seeds_t):
    roots = []
    s = sig_seed + 1j * seeds_t
    for _ in range(40):
        F, dF = F_and_dF(N, s)
        bad = np.abs(dF) < 1e-14
        dF[bad] = 1.0
        step = F / dF
        step = np.where(np.abs(step) > 0.5, step / np.abs(step) * 0.5, step)
        s = s - step
    F, _ = F_and_dF(N, s)
    ok = np.abs(F) < 1e-9
    for z in s[ok]:
        roots.append((z.real, z.imag))
    # dedupe
    ded = {}
    for b, g in roots:
        ded[(round(b, 7), round(g, 6))] = (b, g)
    return list(ded.values())

def winding_count(N, b_lo, b_hi, t_lo, t_hi, ds=0.002):
    """winding number of F_N around rectangle boundary"""
    seg = []
    nt = max(8, int((t_hi - t_lo) / ds)); nb = max(8, int((b_hi - b_lo) / ds))
    seg.append(b_lo + 1j * np.linspace(t_lo, t_hi, nt))
    seg.append(np.linspace(b_lo, b_hi, nb) + 1j * t_hi)
    seg.append(b_hi + 1j * np.linspace(t_hi, t_lo, nt))
    seg.append(np.linspace(b_hi, b_lo, nb) + 1j * t_lo)
    pts = np.concatenate(seg)
    F, _ = F_and_dF(N, pts)
    ph = np.unwrap(np.angle(F))
    return (ph[-1] - ph[0]) / (2 * pi)

def run_one(N):
    rng = np.random.default_rng(12345 + N)
    logN = log(N)
    T0 = 2 * pi * (N + 0.25) ** 2
    tgrid = np.arange(T0, T0 + U, GRID)
    y, lam_sharp = mollifier(N, taper=False)
    _, lam_bv = mollifier(N, taper=True)
    res = {"N": N, "y": y, "T0": T0, "U": U, "logN": logN}

    # ---------- P1: zeros of F_N in the sliver ----------
    sig_seed = 0.5 + 0.5 / logN
    Fline, _ = F_and_dF(N, sig_seed + 1j * tgrid[::2])   # coarse seed line 0.02
    a = np.abs(Fline)
    mins = np.where((a[1:-1] < a[:-2]) & (a[1:-1] < a[2:]))[0] + 1
    seeds = tgrid[::2][mins]
    roots = newton_zeros(N, T0, sig_seed, seeds)
    sliver = [(b, g) for (b, g) in roots
              if T0 <= g <= T0 + U and 0 < b - 0.5 <= 1.2 / logN]
    cvals = sorted((b - 0.5) * logN for (b, g) in sliver)
    Xc = {round(c, 2): sum(1 for v in cvals if v <= c)
          for c in np.arange(0.1, 1.05, 0.1)}
    res["sliver_zero_count_c1"] = Xc[1.0]
    res["X_of_c"] = Xc
    # winding cross-check on 15 random boxes (height 2, sliver width)
    mism = 0
    for _ in range(15):
        tl = T0 + rng.uniform(0, U - 2)
        w = winding_count(N, 0.5 + 1e-4, 0.5 + 1.0 / logN, tl, tl + 2)
        inb = sum(1 for (b, g) in roots
                  if tl < g < tl + 2 and 0.5 + 1e-4 < b < 0.5 + 1.0 / logN)
        if abs(w - inb) > 0.25: mism += 1
    res["winding_mismatches_of_15"] = mism

    # ---------- P2: value distribution of P = F*M on the line ----------
    out = {}
    for tag, lam in (("sharp", lam_sharp), ("bv", lam_bv)):
        c = conv_coeffs(N, y, lam)
        V_pred = float(sum(c[m] ** 2 / m for m in range(2, N * y + 1)))
        Pv = dirichlet_eval(c, 0.5, tgrid)
        V_meas = float(np.mean(np.abs(Pv - 1.0) ** 2))
        rgrid = [0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.6, 0.8]
        Q = {r: float(np.mean(np.abs(Pv) <= r)) for r in rgrid}
        out[tag] = {"V_pred": V_pred, "V_meas": V_meas,
                    "Q_over_r2": {r: Q[r] / r ** 2 for r in rgrid}}
        if tag == "sharp":
            Pline = Pv
    res["P2"] = out

    # ---------- P3: dip intervals at each sliver zero ----------
    V_meas = out["sharp"]["V_meas"]
    kappa = sqrt(2.25 * V_meas)
    c_sh = conv_coeffs(N, y, lam_sharp)
    p3 = []
    for (b, g) in sliver:
        crho = (b - 0.5) * logN
        if crho > 0.5 or crho <= 0.01: continue
        h = b - 0.5
        thr = 4 * kappa * sqrt(12) * crho
        tj = np.arange(g - h, g + h, 2 * h / 400)
        Pj = dirichlet_eval(c_sh, 0.5, tj)
        m = float(np.mean(np.abs(Pj) <= thr) * 2 * h)
        p3.append({"c": crho, "h": h, "meas": m, "pass": bool(m >= h)})
    res["P3"] = {"tested": len(p3),
                 "passed": sum(1 for e in p3 if e["pass"]),
                 "events": p3}
    return res

if __name__ == "__main__":
    with Pool(4) as pool:
        results = pool.map(run_one, NLIST)
    slope_pred = 1.0 / (12 * pi)
    report = {"slope_pred_per_UlogN": slope_pred, "runs": results}
    # P1 adjudication: linearity + slope across N
    for r in results:
        UlogN = r["U"] * r["logN"]
        prof = {c: x / UlogN for c, x in r["X_of_c"].items()}
        r["profile_per_UlogN"] = prof
        cs = sorted(prof)
        num = sum(c * prof[c] for c in cs); den = sum(c * c for c in cs)
        sl = num / den
        r["fit_slope"] = sl
        r["slope_ratio_to_pred"] = sl / slope_pred
        r["max_rel_resid"] = max(abs(prof[c] - sl * c) / max(sl * c, 1e-12)
                                 for c in cs if c >= 0.3)
    with open("mollified_dip_cert.json", "w") as f:
        json.dump(report, f, indent=1, default=str)
    print(json.dumps(report, indent=1, default=str)[:4000])
    print("\n=== SUMMARY ===")
    for r in results:
        print(f"N={r['N']} y={r['y']} sliverX(1)={r['sliver_zero_count_c1']} "
              f"slope_ratio={r['slope_ratio_to_pred']:.3f} "
              f"maxresid={r['max_rel_resid']:.3f} "
              f"windmism={r['winding_mismatches_of_15']} "
              f"V_meas={r['P2']['sharp']['V_meas']:.3f} "
              f"V_pred={r['P2']['sharp']['V_pred']:.3f} "
              f"P3 {r['P3']['passed']}/{r['P3']['tested']}")
        q = r["P2"]["sharp"]["Q_over_r2"]
        print("   Q/r^2:", {k: round(v, 3) for k, v in q.items()})
