#!/usr/bin/env python3
"""Left-band follow-up to casimir_weighted_probe (doc 55 par.8) — adjudicate P-CAS2.

Frozen-term hypothesis: the n=1 coefficient is phase-frozen; mean/std at 1/2 is
ramp 0, sharp ~0.48, iramp ~0.73 -> right-side suppression ordered accordingly,
missing zeros should appear LEFT of the line near it.

PRE-REGISTERED:
  P-CAS2' (prior 0.60): iramp LEFT near-line counts exceed its right counts by
        factor >=3 and are >= the GAF one-sided prediction (mirror pile-up).
  P-CAS2'' (prior 0.55): two-sided near-line totals for ramp and iramp agree
        within x[0.5,2.0] (variance law survives as a TWO-SIDED statement).
"""
import sys
from mpmath import mp, mpc, mpf, pi, log, im, re
mp.dps = 25

def make_F(N, W2):
    L = float(log(N)); ws = [None]*(N+1)
    for n in range(1, N+1):
        y = float(log(n))/L; w2 = W2(y)
        ws[n] = mp.sqrt(w2) if w2 > 0 else mpf(0)
    def F(s):
        return sum(ws[n]*mpf(n)**(-s) for n in range(1, N+1) if ws[n] != 0)
    return F, ws

def winding(g, s_lo, s_hi, t_lo, t_hi, m=200):
    pts = []
    for k in range(m): pts.append(mpc(s_lo + (s_hi-s_lo)*k/m, t_lo))
    for k in range(m): pts.append(mpc(s_hi, t_lo + (t_hi-t_lo)*k/m))
    for k in range(m): pts.append(mpc(s_hi - (s_hi-s_lo)*k/m, t_hi))
    for k in range(m): pts.append(mpc(s_lo, t_hi - (t_hi-t_lo)*k/m))
    pts.append(pts[0])
    tot = mpf(0); prev = g(pts[0])
    for p in pts[1:]:
        cur = g(p); d = cur/prev
        tot += mp.atan2(im(d), re(d)); prev = cur
    return int(round(float(tot/(2*pi))))

def dlogK(ws, N, sig):
    h = mpf(10)**(-10)
    Kp = sum(ws[n]**2*mpf(n)**(-2*(sig+h)) for n in range(1,N+1) if ws[n]!=0)
    Km = sum(ws[n]**2*mpf(n)**(-2*(sig-h)) for n in range(1,N+1) if ws[n]!=0)
    return (mp.log(Kp)-mp.log(Km))/(2*h)

CARRIERS = [('sharp', lambda y: 1.0), ('ramp', lambda y: 2.0*y),
            ('iramp', lambda y: 2.0*(1.0-y))]

if __name__ == '__main__':
    U = mpf(60); half = mpf('0.5'); N = 40
    T = mpf(2)*pi*(N + mpf('0.5'))**2; L = float(log(N))
    print(f"== N={N} U={float(U)} LEFT bands [1/2 - c/logN, 1/2]")
    for name, W2 in CARRIERS:
        F, ws = make_F(N, W2)
        d_half = dlogK(ws, N, half)
        out = []
        for c in [0.5, 1.0, 2.0]:
            d_c = dlogK(ws, N, half - mpf(c)/L)
            pred = float(U/(4*pi)*(d_half - d_c))
            cnt = winding(F, half - mpf(c)/L, half, T, T+U)
            out.append(f"c={c}: {cnt}/{pred:.2f}")
        print(f"  {name:<6} left(det/GAF): " + "  ".join(out))
        sys.stdout.flush()
    print("done")
