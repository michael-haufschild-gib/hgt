#!/usr/bin/env python3
"""z0-optimization for the designed-tower triple (z0*, ell*, N0*) — doc 71.

Budget: creation fraction <= eps* = c_deck/C' = 1/512 (first-pass doc 69).
Split: alpha to the zeta left tail, (1-alpha) to taper Chebyshev (factor 4).
Design: lam0 = exp(-z0*sigma), sigma = sqrt(0.5*loglog T), T = 2*pi*N^2;
        ell = (1-alpha)*eps*.lam0^2/4;  onset: N*ell = 1.
Tiers for the tail bound P(z0) <= alpha*eps*:
  G     : Phi(-z0) = erfc(z0/sqrt2)/2                  (needs BE-effective CLT)
  M2k   : (2k-1)!! * (1+eta) / z0^(2k)                 (needs effective 2k-th moment)
RS floor check: lam0 >= 2*cG*(T/2pi)^(-1/4), cG ~ 1 (bare main sum, Gabcke-grade).
"""
import math

EPS = 1.0/512.0

def dfact(k):  # (2k-1)!!
    r = 1
    for j in range(1, k+1):
        r *= (2*j - 1)
    return r

def phi_tail(z):
    return 0.5*math.erfc(z/math.sqrt(2.0))

def z0_for_tier(tier, k, budget, eta=0.0):
    """smallest z0 with P(z0) <= budget"""
    if tier == 'G':
        lo, hi = 0.5, 50.0
        for _ in range(200):
            mid = 0.5*(lo+hi)
            if phi_tail(mid) <= budget: hi = mid
            else: lo = mid
        return hi
    else:
        return (dfact(k)*(1.0+eta)/budget)**(1.0/(2*k))

def onset_logN(z0, alpha):
    """solve logN = log(4/((1-alpha) eps)) + 2 z0 sqrt(0.5*log(log(2pi)+2logN))"""
    c0 = math.log(4.0/((1.0-alpha)*EPS))
    x = 20.0
    for _ in range(500):
        sigma = math.sqrt(0.5*math.log(math.log(2*math.pi) + 2.0*x))
        xn = c0 + 2.0*z0*sigma
        if abs(xn-x) < 1e-12: x = xn; break
        x = xn
    return x

def triple(tier, k=0, eta=0.0):
    best = None
    for ai in range(1, 100):
        alpha = ai/100.0
        z0 = z0_for_tier(tier, k, alpha*EPS, eta)
        lN = onset_logN(z0, alpha)
        if best is None or lN < best[0]:
            best = (lN, alpha, z0)
    lN, alpha, z0 = best
    T0 = 2*math.pi*math.exp(2*lN)
    sigma = math.sqrt(0.5*math.log(math.log(2*math.pi)+2*lN))
    lam0 = math.exp(-z0*sigma)
    ell = (1-alpha)*EPS*lam0**2/4.0
    rs_floor = 2.0*(T0/(2*math.pi))**(-0.25)   # cG = 1
    return dict(tier=tier, k=k, eta=eta, alpha=alpha, z0=z0, logN0=lN,
                log10T0=math.log10(T0), lam0=lam0, ell=ell,
                rs_ratio=lam0/rs_floor, taper_ints=math.exp(lN)*ell)

print(f"{'tier':>6} {'eta':>4} {'alpha':>5} {'z0*':>6} {'logN0':>7} {'log10 T0':>9} "
      f"{'lam0':>9} {'ell':>9} {'lam0/RSfloor':>12}")
rows = [('G',0)] + [('M',k) for k in (1,2,3,4,5,6,7,8,10,12)]
for eta in (0.0, 1.0):
    for tier,k in rows:
        r = triple(tier,k,eta)
        name = 'G' if tier=='G' else f'M{2*k}'
        print(f"{name:>6} {r['eta']:>4.1f} {r['alpha']:>5.2f} {r['z0']:>6.2f} "
              f"{r['logN0']:>7.1f} {r['log10T0']:>9.1f} {r['lam0']:>9.2e} "
              f"{r['ell']:>9.2e} {r['rs_ratio']:>12.1f}")
    print()

# optimal moment order (eta=0 and 1):
for eta in (0.0,1.0):
    best = min((triple('M',k,eta) for k in range(1,20)), key=lambda r: r['logN0'])
    print(f"optimal moment tier at eta={eta}: k={best['k']} (moment order {2*best['k']}), "
          f"z0*={best['z0']:.2f}, log10 T0 = {best['log10T0']:.1f}")

# sensitivity: eps* better by factor s (constants pass tightening C'/c_deck)
print()
for s in (1,2,4,8):
    EPS_s = s/512.0
    EPS_save = EPS
    globals()['EPS'] = EPS_s
    rG = triple('G'); r7 = triple('M',7)
    print(f"eps* = {s}/512:  G tier log10 T0 = {rG['log10T0']:.1f}   "
          f"M14 tier log10 T0 = {r7['log10T0']:.1f}")
    globals()['EPS'] = EPS_save
