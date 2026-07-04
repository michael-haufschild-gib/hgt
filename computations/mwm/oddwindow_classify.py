#!/usr/bin/env python3
"""
Doc 43 SS7 next round (task #130): fixed refinement + [5830,12000) extension +
per-event shallow/mid-band classification via the PROVED (MOAT-shallow) lemma.

Pipeline fixes vs oddwindow_phase.py: (i) winding-guided subdivision (t-quarters
then sigma-halves) down to ~1.25 x 0.41 sub-box BEFORE findroot; (ii) strict
acceptance sigma in [0.53,1.35], t in hit box, |Phi(root)| < 1e-20; (iii) all
prior events re-refined with the same pipeline; (iv) coefficient array length
50 (N reaches 44 at T = 12000; the earlier module default 31 would silently
truncate).

Classification (doc 43 SS6): event shallow  <=>  eta^2 * M_r/(r-eta)^2 <= E*(t0),
r = 0.5, M_r = max_{64 pts}|Phi(s0 + r e^{i theta})|,
E*(t0) = |gamma(1/2+it0)| * (t0/2pi)^{-1/4}   (completed-normalization AFE
proxy, constant 1 stated as proxy pending the cofinality write-out).

PRE-REGISTERED (before run):
  P-D1' (prior 0.55): n >= 30 clean events and mean |p - nearest int| <= 0.18.
  P-D2' (prior 0.85): all eta < 0.30 (no deep pairs).
  P-D3  (prior 0.50): >= 40% of clean events are SHALLOW (killed by the proved
        lemma); the surviving mid-band fraction (<= 60%) is the measured wall.
"""
from mpmath import (mp, mpc, mpf, pi, sqrt, floor, findroot, re, im, fabs,
                    gamma as Gamma, exp)
from euler_suppression_boxcount import make_phi, coeffs, winding
from multiprocessing import Pool

NC = 50

def sweep_chunk(args):
    t_lo, t_hi = args
    mp.dps = 25
    a = coeffs('E', 0, NC)
    hits = []
    T = mpf(t_lo)
    while T < t_hi:
        N = int(floor(sqrt(T / (2 * pi))))
        phi = make_phi(a, N)
        w, susp = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5)
        if susp:
            w, _ = winding(phi, mpf('0.53'), mpf('1.35'), T, T + 5, m=320)
        if w != 0:
            hits.append((float(T), N, w))
        T += 5
    return hits

def refine_guided(T0, N):
    mp.dps = 30
    a = coeffs('E', 0, NC)
    phi = make_phi(a, N)
    slo, shi = mpf('0.53'), mpf('1.35')
    tlo, thi = mpf(T0), mpf(T0) + 5
    # t-subdivision to width 1.25, then one sigma split
    for _ in range(2):
        tm = (tlo + thi) / 2
        w1, _ = winding(phi, slo, shi, tlo, tm, m=120)
        if w1 != 0:
            thi = tm
        else:
            tlo = tm
    sm = (slo + shi) / 2
    wl, _ = winding(phi, slo, sm, tlo, thi, m=120)
    if wl != 0:
        shi = sm
    else:
        slo = sm
    mp.dps = 40
    seeds = [mpc((slo+shi)/2, (tlo+thi)/2),
             mpc((slo+shi)/2, (3*tlo+thi)/4),
             mpc((slo+shi)/2, (tlo+3*thi)/4)]
    for s0 in seeds:
        try:
            r = findroot(phi, s0, solver='muller', tol=mpf('1e-30'))
            if (mpf('0.53') < re(r) < mpf('1.35') and T0 - mpf('0.1') < im(r)
                    < T0 + mpf('5.1') and fabs(phi(r)) < mpf('1e-20')):
                return r
        except Exception:
            pass
    return None

def classify(rho, N):
    mp.dps = 40
    a = coeffs('E', 0, NC)
    phi = make_phi(a, N)
    t0 = im(rho)
    eta = re(rho) - mpf('0.5')
    s0 = mpc(mpf('0.5'), t0)
    r = mpf('0.5')
    Mr = max(fabs(phi(s0 + r * exp(mpc(0, 2 * pi * k / 64))))
             for k in range(64))
    Estar = fabs(pi ** (-s0 / 2) * Gamma(s0 / 2)) * (t0 / (2 * pi)) ** mpf('-0.25')
    shallow = eta ** 2 * Mr / (r - eta) ** 2 <= Estar
    margin = float(eta ** 2 * Mr / ((r - eta) ** 2 * Estar))
    return eta, shallow, margin

BANKED = [(220.0,5),(415.0,8),(635.0,10),(725.0,10),(945.0,12),
          (5010.0,28),(5225.0,28),(5360.0,29),(5425.0,29),
          (1328.0,14),(1343.0,14),(1413.0,14),(1626.0,16),(1766.0,16),
          (1814.0,16),(1829.0,17),(1889.0,17),(2247.0,18),(2295.0,19),
          (2300.0,19),(2495.0,19),(2816.0,21),(2941.0,21),(3447.0,23),
          (3590.0,23),(3680.0,24),(3863.0,24),(3883.0,24),(3898.0,24),
          (3938.0,25),(4251.0,26),(4309.0,26),(4344.0,26),(4474.0,26),
          (4587.0,27),(4870.0,27),(4990.0,28)]

if __name__ == "__main__":
    chunks = [(5830 + 386*k, min(5830 + 386*(k+1), 12000)) for k in range(16)]
    with Pool(16) as pool:
        res = pool.map(sweep_chunk, chunks)
    new = [h for c in res for h in c]
    print(f"new odd boxes in [5830,12000): {len(new)}")
    allh = BANKED + [(T, N) for (T, N, w) in new]
    ps, etas, shal = [], [], []
    for T0, N in allh:
        rho = refine_guided(T0, N)
        if rho is None:
            print(f"  T={T0}: REFINE FAILED (guided)")
            continue
        eta, sh, mg = classify(rho, N)
        pfrac = float(sqrt(im(rho) / (2 * pi))) % 1.0
        ps.append(pfrac); etas.append(float(eta)); shal.append(bool(sh))
        print(f"  T={T0} N={N}: rho={float(re(rho)):.5f}+{float(im(rho)):.4f}i "
              f"p={pfrac:.3f} eta={float(eta):.3f} "
              f"{'SHALLOW' if sh else 'MID-BAND'} (lemma-margin {mg:.2f})")
    n = len(ps)
    dist = [min(p, 1 - p) for p in ps]
    md = sum(dist) / n
    fs = sum(shal) / n
    print(f"\nn = {n} clean events (of {len(allh)})")
    print(f"P-D1' mean |p-int| = {md:.4f}: "
          f"{'PASS' if (n >= 30 and md <= 0.18) else 'FAIL'}")
    print(f"P-D2' max eta = {max(etas):.3f}: "
          f"{'PASS' if max(etas) < 0.30 else 'FAIL'}")
    print(f"P-D3 shallow fraction = {fs:.2f}: "
          f"{'PASS' if fs >= 0.40 else 'FAIL'}  "
          f"(measured wall = mid-band fraction {1-fs:.2f})")
