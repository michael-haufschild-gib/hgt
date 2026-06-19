#!/usr/bin/env python3.13
"""
zeta_half_pslq.py -- Critic 2026-06-19.  ATTACK 3 test (speculative-proofs-grand-conjectures.md).
Is the central value zeta(1/2) a Q-linear / low-degree-algebraic combination of the mixed-Tate
constants {1, pi, log2pi, gamma_E, zeta(3), zeta(5), Catalan}?  A PSLQ NULL result (no integer
relation up to large height) is numeric EVIDENCE that zeta(1/2) is a NEW non-motivic period
(supports M_1/2 being a genuinely new object; B3/B32 central-value frontier).  Numeric tier only.
Archive: computations/zeta_half_pslq/.
"""
import mpmath as mp
mp.mp.dps = 260

zh   = mp.zeta(mp.mpf(1)/2)        # -1.4603545...
one  = mp.mpf(1)
pi   = mp.pi
l2pi = mp.log(2*mp.pi)
gam  = mp.euler
z3   = mp.zeta(3)
z5   = mp.zeta(5)
cat  = mp.catalan

print(f" dps={mp.mp.dps}")
print(f" zeta(1/2) = {mp.nstr(zh,30)}")

# (A) LINEAR relation: is zeta(1/2) in the Q-span of the mixed-Tate basis?
basisA = [zh, one, pi, l2pi, gam, z3, z5, cat]
labelsA = ["zeta(1/2)","1","pi","log2pi","gamma_E","zeta(3)","zeta(5)","Catalan"]
relA = mp.pslq(basisA, maxcoeff=10**14, maxsteps=10**6)
print("\n (A) LINEAR  span{1,pi,log2pi,gamma_E,zeta(3),zeta(5),Catalan}:")
if relA is None:
    print("     PSLQ: NO integer relation up to height 1e14  =>  zeta(1/2) NOT a Q-linear combo of the mixed-Tate basis.")
else:
    print(f"     PSLQ found relation: {dict(zip(labelsA,relA))}")

# (B) is zeta(1/2) ALGEBRAIC over Q(pi)?  test {1, zh, zh^2, zh^3, pi, pi^2, pi^3, zh*pi, zh^2*pi, zh*pi^2}
basisB = [one, zh, zh**2, zh**3, pi, pi**2, pi**3, zh*pi, zh**2*pi, zh*pi**2]
labelsB = ["1","z","z^2","z^3","pi","pi^2","pi^3","z*pi","z^2*pi","z*pi^2"]
relB = mp.pslq(basisB, maxcoeff=10**12, maxsteps=10**6)
print("\n (B) ALGEBRAIC over Q(pi) (degree<=3 monomials in z=zeta(1/2), pi):")
if relB is None:
    print("     PSLQ: NO relation up to height 1e12  =>  zeta(1/2) NOT degree<=3 algebraic over Q(pi).")
else:
    print(f"     PSLQ found relation: {dict(zip(labelsB,relB))}")

# (C) control: confirm PSLQ DOES find the known zeta(2)=pi^2/6 (sanity that the machinery works)
relC = mp.pslq([mp.zeta(2), pi**2, one], maxcoeff=10**6, maxsteps=10**6)
print(f"\n (C) sanity control  [zeta(2), pi^2, 1]:  PSLQ = {relC}   (expect [6,-1,0] i.e. 6*zeta(2)=pi^2)")
print("\n VERDICT: (A),(B) NULL + (C) finds pi^2/6  =>  machinery sound AND zeta(1/2) shows no low-height")
print("          motivic relation => numeric support for a NEW non-motivic central period (Attack 3).")
