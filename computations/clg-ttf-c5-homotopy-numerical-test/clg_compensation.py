#!/usr/bin/env python3
"""Numerical test of the CLG/TTF open core: positivity of
   thetaCuspC5LikelihoodHomotopyCompensationThree u t l  on 0 <= l <= 1, for 0 < t <= u.
Every formula is transcribed from the Lean definitions (files ThetaCusp*.lean, RHTower):
  gap n = n^2-1;  B(x) = pi e^{2x} - 3/2;  A(x) = pi e^{2x};
  mu = sum_{n>=2} [ w_n delta_{gap n} + r_n Leb|(gap n, inf) ],  w_n = e^{-3gap/2} n^4,  r_n = e^{-3gap/2} (3/2) n^2 gap;
  Z(B) = 1 + int e^{-Bt} dmu;  M_m(B) = int t^m e^{-Bt} dmu;  Mean = M1/Z; Var = M2/Z - Mean^2; K3 = M3/Z - 3 Mean M2/Z + 2 Mean^3;
  LP(x) = log Z(B(x)); LPJ1 = -2A Mean; LPJ2 = 4A^2 Var - 4A Mean; LPJ3 = -8A^3 K3 + 24 A^2 Var - 8 A Mean;
  lambda(A) = 3A/(A-3/2)^2; F(A,z) = 1 - lambda z; Slope = 2A + lambda/F; d(A) = -6A(A+3/2)/(A-3/2)^3;
  homotopy data at (u,t): A = A(u), z = cosh 2t - 1, z' = 2 sinh 2t, ... (see Lean thetaCuspC5LikelihoodHomotopyData)."""
import sys, json
from mpmath import mp, mpf, exp, log, cosh, sinh, pi, factorial, nstr
from multiprocessing import Pool
mp.dps = 30
NMAX = 40

def gap(n): return mpf(n)**2 - 1
def Bcoord(x): return pi*exp(2*x) - mpf(3)/2
def Ascale(x): return pi*exp(2*x)

def moments(B):
    """Z, M1, M2, M3"""
    Z = mpf(1); M = [mpf(0)]*4
    for n in range(2, NMAX+1):
        g = gap(n); e3 = exp(-mpf(3)/2*g); w = e3*mpf(n)**4; r = e3*mpf(3)/2*mpf(n)**2*g
        eB = exp(-B*g)
        Z += w*eB + r*eB/B
        for m in range(1, 4):
            # int_g^inf t^m e^{-Bt} dt = e^{-Bg} sum_{j=0}^m m!/j! g^j / B^{m-j+1}
            ray = eB*sum(factorial(m)/factorial(j)*g**j/B**(m-j+1) for j in range(m+1))
            M[m] += w*g**m*eB + r*ray
    return Z, M[1], M[2], M[3]

def LPjets(x):
    B = Bcoord(x); A = Ascale(x)
    Z, M1, M2, M3 = moments(B)
    mean = M1/Z; var = M2/Z - mean**2; k3 = M3/Z - 3*mean*(M2/Z) + 2*mean**3
    LP = log(Z)
    J1 = -2*A*mean
    J2 = 4*A**2*var - 4*A*mean
    J3 = -8*A**3*k3 + 24*A**2*var - 8*A*mean
    return LP, J1, J2, J3

def data(u, t):
    A = Ascale(u); z = cosh(2*t) - 1; zp = 2*sinh(2*t)
    lam = 3*A/(A - mpf(3)/2)**2; F = 1 - lam*z; slope = 2*A + lam/F
    d = -6*A*(A + mpf(3)/2)/(A - mpf(3)/2)**3
    LPu, J1u, J2u, J3u = LPjets(u); LPp, J1p, J2p, J3p = LPjets(u+t); LPm, J1m, J2m, J3m = LPjets(u-t)
    D = {}
    D['t'] = t
    D['q'] = 2*A*z - log(F);                    D['dq'] = 2*LPu - LPp - LPm
    D['a'] = slope*zp;                          D['da'] = J1m - J1p
    D['b'] = 4*(lam**2/F**2)*z*(z+2) + 4*slope*(z+1);  D['db'] = -J2p - J2m
    D['c'] = zp*(8*(lam**3/F**3)*z*(z+2) + 12*(lam**2/F**2)*(z+1) + 4*slope);  D['dc'] = J3m - J3p
    D['s'] = 4*A*z + d*z/F;                      D['ds'] = 2*J1u - J1p - J1m
    D['m'] = (4*A + d/F**2)*zp;                  D['dm'] = J2m - J2p
    D['n'] = 4*(2*lam*d/F**3*z*(z+2) + (4*A + d/F**2)*(z+1));  D['dn'] = -J3p - J3m
    return D

def comp3(D, l):
    t = D['t']
    aff = lambda x, dx: x + l*dx
    jet1 = aff(D['a'], D['da']); jet2 = aff(D['b'], D['db']); jet3 = aff(D['c'], D['dc'])
    sA = aff(D['s'], D['ds']); sM1 = aff(D['m'], D['dm']); sM2 = aff(D['n'], D['dn'])
    act = aff(D['q'], D['dq'])
    vC = jet1*(t*sM1) - (jet1 + t*jet2)*sA
    vC1 = D['da']*(t*sM1) + jet1*(t*D['dm']) - (D['da'] + t*D['db'])*sA - (jet1 + t*jet2)*D['ds']
    vC2 = 2*(D['da']*(t*D['dm']) - (D['da'] + t*D['db'])*D['ds'])
    vS = jet1*(t*sM1 + t**2*sM2) - (jet1 + 3*t*jet2 + t**2*jet3)*sA
    e = exp(act); r = e - 1; dq = D['dq']
    bR = 1/r; bR1 = -e*dq/r**2; bR2 = e*(e+1)*dq**2/r**3; bR3 = -e*(e**2 + 4*e + 1)*dq**3/r**4
    v = t*jet1; dv = t*D['da']
    bC = 14 + 10*v + 8*v*bR
    bC1 = 10*dv + 8*(dv*bR + v*bR1)
    bC2 = 8*(2*dv*bR1 + v*bR2)
    bC3 = 8*(3*dv*bR2 + v*bR3)
    c3 = -(bC3*vC + 3*bC2*vC1 + 3*bC1*vC2)
    c0 = 5*vS - bC*vC
    return c3, c0, act, vC

def scan(args):
    u, ts = args
    mp.dps = 30
    out = []
    for t in ts:
        D = data(u, t)
        vals = [(l, comp3(D, l)) for l in [mpf(k)/20 for k in range(21)]]
        c3min = min(v[1][0] for v in vals); lmin = min(vals, key=lambda v: v[1][0])[0]
        c0 = [v[1][1] for v in vals]
        out.append(dict(u=float(u), t=float(t), Aut=float(Ascale(u-t)), c3min=float(c3min), l_at_min=float(lmin),
                        c3_ends=[float(vals[0][1][0]), float(vals[-1][1][0])], comp_ends=[float(c0[0]), float(c0[-1])],
                        action_ends=[float(vals[0][1][2]), float(vals[-1][1][2])], dq=float(D['dq'])))
    return out

if __name__ == "__main__":
    us = [mpf(k)/40 for k in range(1, 121)]             # u in (0, 3]
    jobs = [(u, [u*mpf(j)/24 for j in range(1, 25)]) for u in us]   # t in (0, u]
    with Pool(8) as pool:
        res = pool.map(scan, jobs)
    flat = [r for rr in res for r in rr]
    json.dump(flat, open("clg_scan.json", "w"))
    neg = [r for r in flat if r["c3min"] <= 0]
    print("points:", len(flat), " negative c3:", len(neg))
    for r in sorted(neg, key=lambda r: r["c3min"])[:15]:
        print("u=%.3f t=%.4f A(u-t)=%.2f c3min=%.4g at l=%.2f ends=%s comp_ends=%s dq=%.3g" % (r["u"], r["t"], r["Aut"], r["c3min"], r["l_at_min"], r["c3_ends"], r["comp_ends"], r["dq"]))
    pos6 = [r for r in flat if r["Aut"] >= 6]
    print("points with A(u-t)>=6:", len(pos6), " negative among them:", len([r for r in pos6 if r["c3min"] <= 0]))
    print("sample:", [(round(r["u"],2), round(r["t"],3), "%.3g" % r["c3min"]) for r in flat[::150]])
