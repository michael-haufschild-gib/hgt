#!/usr/bin/env python3
"""
Doc 46 SS4 (3): out-of-sample census decade [20000, 30000) for the (HOLD) model.
Same engine as oddwindow_classify (guided refinement, MOAT-shallow classify,
NC = 75 for N up to 69).
PRE-REGISTERED:
  P-H1 (prior 0.65): every NEW mid-band survivor has |p - nearest int| <= 0.18
       (the (HOLD) cutoff p* holds out-of-sample).
  P-H2 (prior 0.55): the deepest new survivor has |p - nearest int| <= 0.10
       (deeper pairs sit at tighter phases).
"""
from mpmath import mp, mpc, mpf, pi, sqrt, floor, findroot, re, im, fabs, gamma as Gamma, exp
from euler_suppression_boxcount import make_phi, coeffs, winding
from multiprocessing import Pool
NC = 75

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
    for _ in range(2):
        tm = (tlo + thi) / 2
        w1, _ = winding(phi, slo, shi, tlo, tm, m=120)
        if w1 != 0: thi = tm
        else: tlo = tm
    sm = (slo + shi) / 2
    wl, _ = winding(phi, slo, sm, tlo, thi, m=120)
    if wl != 0: shi = sm
    else: slo = sm
    mp.dps = 40
    for s0 in (mpc((slo+shi)/2, (tlo+thi)/2), mpc((slo+shi)/2, (3*tlo+thi)/4),
               mpc((slo+shi)/2, (tlo+3*thi)/4)):
        try:
            r = findroot(phi, s0, solver='muller', tol=mpf('1e-30'))
            if (mpf('0.53') < re(r) < mpf('1.35') and T0-mpf('0.1') < im(r)
                    < T0+mpf('5.1') and fabs(phi(r)) < mpf('1e-18')):
                return r
        except Exception:
            pass
    return None

if __name__ == "__main__":
    chunks = [(20000 + 625*k, min(20000 + 625*(k+1), 30000)) for k in range(16)]
    with Pool(16) as pool:
        res = pool.map(sweep_chunk, chunks)
    hits = [h for c in res for h in c]
    print(f"odd boxes in [20000,30000): {len(hits)}")
    a = coeffs('E', 0, NC)
    surv = []
    for T0, N, w in hits:
        rho = refine_guided(T0, N)
        if rho is None:
            print(f"  T={T0}: REFINE FAILED"); continue
        t0 = im(rho); eta = re(rho) - mpf('0.5')
        s0 = mpc(mpf('0.5'), t0); r = mpf('0.5')
        phi = make_phi(a, N)
        Mr = max(fabs(phi(s0 + r*exp(mpc(0, 2*pi*k/64)))) for k in range(64))
        Estar = fabs(pi**(-s0/2)*Gamma(s0/2))*(t0/(2*pi))**mpf('-0.25')
        sh = eta**2*Mr/((r-eta)**2*Estar) <= 1
        p = float(sqrt(t0/(2*pi))) % 1.0
        d = min(p, 1-p)
        print(f"  T={T0} N={N}: eta={float(eta):.3f} p={p:.3f} "
              f"{'SHALLOW' if sh else 'MID-BAND'}")
        if not sh: surv.append((d, float(eta)))
    if surv:
        print(f"\nmid-band survivors: {len(surv)}; max |p-int| = "
              f"{max(d for d,_ in surv):.3f}")
        dm = max(surv, key=lambda x: x[1])
        print(f"P-H1: {'PASS' if max(d for d,_ in surv) <= 0.18 else 'FAIL'}")
        print(f"P-H2 deepest (eta={dm[1]:.3f}) at |p-int|={dm[0]:.3f}: "
              f"{'PASS' if dm[0] <= 0.10 else 'FAIL'}")
    else:
        print("no mid-band survivors in decade (P-H1 vacuous PASS)")
