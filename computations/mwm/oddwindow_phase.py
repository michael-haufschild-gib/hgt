#!/usr/bin/env python3
"""
Task #130 attack, (DISC-fin)-unconditional (doc 43): RS-phase statistics of the
odd windows of the exact-FE truncation (E-class carrier, a_n = 1).

Sweep the unswept band T in [1030, 5000) (delta t = 5, N = floor(sqrt(T/2pi)),
same box/winding engine as runs 5/7) and for EVERY odd box (this band + the 9
banked events from run 7) record:
  p   = frac(sqrt(T0/2pi)) at the refined zero height (RS phase / truncation
        transition coordinate),
  eta = Re(rho) - 1/2 (pair depth).

PRE-REGISTERED (before run):
  P-D1 (prior 0.5): with n >= 25 events total, the mean distance of p to the
       nearest integer is <= 0.17 (uniform expects 0.25): odd events cluster at
       truncation transitions.  PASS => the exceptional set is p-localized:
       (SD-parity) becomes a p-locus target and #144's traversal can dodge it.
       FAIL => transition-birth is not the mechanism; pivot to the deep-valley
       (large-deviation) statistic.
  P-D2 (prior 0.7): all pair depths eta lie below 0.35 (no deep pairs at these
       heights; consistent with the shallow-moat lemma carrying the measured
       events).
"""
from mpmath import mp, mpc, mpf, pi, sqrt, floor, findroot, re, im, fabs
from euler_suppression_boxcount import make_phi, coeffs, winding
from multiprocessing import Pool

def sweep_chunk(args):
    t_lo, t_hi = args
    mp.dps = 25
    a = coeffs('E', 0)
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

def refine(T0, N):
    mp.dps = 40
    a = coeffs('E', 0)
    phi = make_phi(a, N)
    try:
        r = findroot(phi, mpc('0.8', T0 + 2.5), solver='muller', tol=mpf('1e-30'))
        return r
    except Exception:
        return None

if __name__ == "__main__":
    chunks = [(1030 + 248*k, min(1030 + 248*(k+1), 5000)) for k in range(16)]
    with Pool(16) as pool:
        res = pool.map(sweep_chunk, chunks)
    hits = [h for c in res for h in c]
    print(f"new odd boxes in [1030,5000): {len(hits)}")
    banked = [(220.0,5),(415.0,8),(635.0,10),(725.0,10),(945.0,12),
              (5010.0,28),(5225.0,28),(5360.0,29),(5425.0,29)]
    allh = [(T,N) for (T,N,w) in hits] + banked
    ps, etas = [], []
    for T0, N in allh:
        r = refine(T0, N)
        if r is None or not (0.5 < re(r) < 1.4 and T0-1 < im(r) < T0+6):
            print(f"  T={T0}: refine failed/left box")
            continue
        pfrac = float(sqrt(im(r)/(2*pi))) % 1.0
        eta = float(re(r)) - 0.5
        ps.append(pfrac); etas.append(eta)
        print(f"  T={T0} N={N}: rho = {float(re(r)):.5f}+{float(im(r)):.4f}i  "
              f"p = {pfrac:.3f}  eta = {eta:.3f}")
    dist = [min(p, 1-p) for p in ps]
    mean_d = sum(dist)/len(dist)
    print(f"\nn = {len(ps)} events; mean |p - nearest int| = {mean_d:.4f} "
          f"(uniform: 0.25)")
    print(f"P-D1: {'PASS' if (len(ps) >= 25 and mean_d <= 0.17) else 'FAIL'}")
    print(f"P-D2 max eta = {max(etas):.3f}: "
          f"{'PASS' if max(etas) < 0.35 else 'FAIL'}")
