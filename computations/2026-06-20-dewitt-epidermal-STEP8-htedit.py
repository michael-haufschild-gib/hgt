#!/usr/bin/env python3
# MACHINE STEP8: minimal edit of the boundary-determines-bulk NODE test toward HT + not-HT-blind.
# NODE: interior = (harmonic/Cauchy) extension of boundary data. Edit: use a real HT function's boundary
# values on a circle, reconstruct the interior via the Cauchy integral, and compare to a NON-HT analytic
# control (exp). If the reconstruction error is the SAME for HT (zeta) and non-HT (exp), the constraint is
# HT-BLIND (boundary-determines-bulk holds for ALL functions analytic in the disk, by Cauchy's theorem).
import mpmath as mp
mp.mp.dps = 30

def cauchy_interior(f, center, R, z0, M=400):
    # u(z0) = (1/2pi i) oint f(z)/(z-z0) dz over circle |z-center|=R
    s = mp.mpf(0)
    for k in range(M):
        th = 2*mp.pi*k/M
        z = center + R*mp.e**(1j*th)
        dz = 1j*R*mp.e**(1j*th)*(2*mp.pi/M)
        s += f(z)/(z-z0)*dz
    return s/(2j*mp.pi)

tests = [
    ("exp (NON-HT analytic control)", mp.e**(1+0j) and (lambda z: mp.e**z), mp.mpc(4,0), 1.0, mp.mpc(4.3,0.2)),
    ("Gamma (HT)",                    lambda z: mp.gamma(z),                 mp.mpc(4,0), 1.0, mp.mpc(4.3,0.2)),
    ("zeta (HT)",                     lambda z: mp.zeta(z),                  mp.mpc(4,0), 1.0, mp.mpc(4.3,0.2)),
]
print("=== STEP8: interior Cauchy-reconstruction error (boundary determines bulk) ===")
print("  function                         | reconstructed       | true                | |error|")
errs={}
for name, f, c, R, z0 in tests:
    rec = cauchy_interior(f, c, R, z0)
    tru = f(z0)
    e = abs(rec-tru)
    errs[name]=e
    print(f"  {name:32s} | {mp.nstr(rec,8):>18} | {mp.nstr(tru,8):>18} | {mp.nstr(e,3)}")
print("\nREAD: if HT (Gamma,zeta) and NON-HT (exp) reconstruct to the SAME (~machine) accuracy, the")
print("boundary-determines-bulk constraint is HT-BLIND (Cauchy's theorem holds for ALL analytic functions).")
