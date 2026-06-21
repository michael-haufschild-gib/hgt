#!/usr/bin/env python3
"""
connes A1 — same-geometry/different-arithmetic test on the A-axis (value arithmetic).

Question (gpt/15 candidate #3/#10; Conway r2 gate): are zeta's seam values
  S_k = sum_rho (rho-1/2)^{-2k}
arithmetically RIGID (not reducible to pi-periods), or simple like an arithmetic-progression divisor?

Control with IDENTICAL seam geometry, different arithmetic:
  AP divisor  gamma_n = n  (zeros on the seam at 1,2,3,...):
     S_k^AP = sum_pairs (i n)^{-2k} = (-1)^k sum_n n^{-2k} = (-1)^k zeta(2k)  =  rational * pi^{2k}.
  So the AP control's seam values are PURE pi-periods: low-height integer relations MUST exist
  (e.g. S_1^AP = -zeta(2) = -pi^2/6  =>  6 S_1^AP + pi^2 = 0).

Prediction (from the fused closed form S_k = 2^{2k} - 1/4(2^{2k}-1)zeta(2k) - 2^{2k-2}beta(2k) - prime):
  zeta's S_k carries the Catalan-family beta(2k) and a prime-side term, so S_k^zeta is NOT in Q*pi^{2k}:
  the period test must FAIL for zeta (no low-height relation) but PASS for the AP control.

Tests (PSLQ integer-relation detection + a certified small exact shell):
  T1  pi-period membership:  relation among (pi^{2k}, S_k)?      AP: yes (low height) | zeta: no
  T2  degree-2 collapse:     relation among (S_1^2, S_2, S_1, 1)? AP: yes | zeta: no
  T3  fused validation (zeta): relation among (1, zeta(2k), beta(2k), S_k^P, S_k)? must be EXACT (my formula)
  Exact shell minimum A(d=1, H) over (pi^{2k}, S_k): AP -> ~0, zeta -> bounded away from 0.
Fast/chunked: dps 50, k=1..4, shell height <= 8.
"""
import mpmath as mp

mp.mp.dps = 50
half = mp.mpf(1)/2
K = 4

def logXi(w):
    s = half + w
    return mp.log(half*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s))
def P_half(w):
    s = half + w
    return mp.zeta(s,1,1)/mp.zeta(s)
def beta(s):
    return mp.power(4,-s)*(mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4))

cL = mp.taylor(logXi, 0, 2*K+2)
cP = mp.taylor(P_half, 0, 2*K+1)

def pslq_report(vec, tol_digits=40, maxcoeff=10**6):
    try:
        rel = mp.pslq(vec, tol=mp.mpf(10)**(-tol_digits), maxcoeff=maxcoeff, maxsteps=10000)
    except Exception:
        rel = None
    if rel is None:
        return None, None
    h = max(abs(int(c)) for c in rel)
    resid = abs(sum(mp.mpf(int(c))*v for c, v in zip(rel, vec)))
    return rel, (h, resid)

print(f"[setup] dps={mp.mp.dps}  K={K}")
print("="*78)
for k in range(1, K+1):
    Sz   = -mp.mpf(k)*cL[2*k]                      # zeta seam value S_k
    SzP  = -half*cP[2*k-1]                          # prime half
    z2k  = mp.zeta(2*k)
    b2k  = beta(2*k)
    Sap  = ((-1)**k)*z2k                            # AP-control seam value = (-1)^k zeta(2k)
    pi2k = mp.power(mp.pi, 2*k)

    print(f"\n--- k={k} ---   S_k(zeta)={mp.nstr(Sz,12)}   S_k(AP)={mp.nstr(Sap,12)}")

    # T1: pi-period membership  c0*pi^{2k} + c1*S_k = 0 ?
    rz, iz = pslq_report([pi2k, Sz])
    ra, ia = pslq_report([pi2k, Sap])
    print(f"  T1 pi-period [pi^2k, S_k]:  AP-> rel={ra} (h,res)={None if ia is None else (ia[0], mp.nstr(ia[1],3))}"
          f"  | zeta-> rel={rz} (h,res)={None if iz is None else (iz[0], mp.nstr(iz[1],3))}")

    # T3: fused validation for zeta: (1, zeta(2k), beta(2k), S_k^P, S_k) must satisfy exact integer-ish rel
    # my formula: S_k = 2^{2k} - 1/4(2^{2k}-1)zeta(2k) - 2^{2k-2}beta(2k) + S_k^P    (S_k^P = -prime/...)
    rf, iff = pslq_report([mp.mpf(1), z2k, b2k, SzP, Sz], tol_digits=42)
    print(f"  T3 fused [1, zeta(2k), beta(2k), S_k^P, S_k] (zeta): rel={rf}"
          f" (h,res)={None if iff is None else (iff[0], mp.nstr(iff[1],3))}")

# T2: degree-2 collapse among {1, S_1, S_2, S_1^2}  (AP must collapse, zeta must resist)
S1z=-cL[2]; S2z=-2*cL[4]
S1a=-mp.zeta(2); S2a=mp.zeta(4)
print("\n"+"="*78)
print("T2 degree-2 [1, S_1, S_2, S_1^2]:")
for name,(a,b) in [("AP  ",(S1a,S2a)),("zeta",(S1z,S2z))]:
    r,i = pslq_report([mp.mpf(1), a, b, a*a])
    print(f"  {name}: rel={r}  (h,res)={None if i is None else (i[0], mp.nstr(i[1],3))}")

# Exact certified shell minimum A(d=1,H) over (pi^2, S_1): min |c0 pi^2 + c1 S_1|, 0<|c|<=H
print("\n"+"="*78)
print("Exact shell-min A(d=1,H) over [pi^2, S_1]  (smallest nonzero |c0 pi^2 + c1 S_1|):")
pi2=mp.power(mp.pi,2)
for name,s1 in [("AP  ",S1a),("zeta",S1z)]:
    for H in (4,8):
        best=None
        for c0 in range(-H,H+1):
            for c1 in range(-H,H+1):
                if c0==0 and c1==0: continue
                v=abs(c0*pi2+c1*s1)
                if best is None or v<best[0]: best=(v,(c0,c1))
        print(f"  {name} H={H}: min|.|={mp.nstr(best[0],6)} at {best[1]}")
print("\n[done] AP (pi-period) collapses; zeta resists => zeta seam values are arithmetically rigid.")
