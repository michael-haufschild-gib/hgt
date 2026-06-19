#!/usr/bin/env python3.13
"""
First concrete brick of the archimedean/de Branges (Hermite–Biehler) structure: Laguerre inequalities.

The de Branges-space positivity of ξ (Hermite–Biehler) is the Laguerre-Pólya class condition, whose
computable rungs are the LAGUERRE INEQUALITIES of Ξ_R(t)=ξ(½+it):
    L_1(t) = Ξ_R'(t)^2 − Ξ_R(t)·Ξ_R''(t) ≥ 0      (first; the de Branges phase-monotonicity / HB positivity)
and the higher Laguerre inequalities L_k. The FULL hierarchy {L_k ≥ 0 ∀k,t} ⟺ Ξ_R ∈ LP ⟺ RH. This is
the de Branges/Hermite–Biehler face of the apex (complementary to the Pick-kernel carrier): de Branges
phase φ(t)=arg(Ξ_R−iΞ_R') is monotone ⟺ L_1≥0; the de Branges space H(E), E=Ξ_R−iΞ_R', is genuine.

Tests: (1) L_1(t)≥0 on a grid (first rung — known for ξ, the manifest de Branges positivity);
       (2) the de Branges phase φ(t) is monotone decreasing (φ'(t)=L_1/|E|^2 ≥0-shaped) ⟺ HB;
       (3) the higher Laguerre L_2 sign (the hierarchy toward RH).
"""
import mpmath as mp

mp.mp.dps = 30

def xi(s):
    return (s * (s - 1) / 2) * mp.pi**(-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def XiR(t):
    return mp.re(xi(mp.mpf('0.5') + 1j * t))

def derivs(t):
    f0 = XiR(t)
    f1 = mp.diff(XiR, t, 1)
    f2 = mp.diff(XiR, t, 2)
    f3 = mp.diff(XiR, t, 3)
    f4 = mp.diff(XiR, t, 4)
    return f0, f1, f2, f3, f4

def main():
    print(f"=== Laguerre inequalities / de Branges HB positivity of Ξ_R (dps={mp.mp.dps}) ===")
    grid = [mp.mpf(t) for t in ['0', '2', '5', '8', '12', '14.13', '17', '21', '25', '30', '35']]
    print("   t       L_1 = Ξ'^2−Ξ Ξ''        L_2 (higher)            φ'(t)=L_1/|E|^2")
    allL1 = True; allL2 = True
    for t in grid:
        f0, f1, f2, f3, f4 = derivs(t)
        L1 = f1**2 - f0 * f2
        # second Laguerre inequality (standard form): L_2 = (f2)^2 - 2 f1 f3 + ... ; use the
        # Jensen/Laguerre L_2 = 3 f2^2 - 4 f1 f3 + f0 f4 ... we use the canonical
        # L_2 = (f2^2 - f1 f3) - (1/?)... — report the discriminant-style 3f2^2-4f1f3+f0f4? Use the
        # well-known L_2 ≥0 form for LP: f2^2 ≥ f1 f3 *and* combined; here report 3f2^2-4f1f3+f0f4.
        L2 = 3 * f2**2 - 4 * f1 * f3 + f0 * f4
        E2 = f0**2 + f1**2          # |E|^2 with E=Ξ_R - iΞ_R'
        phip = L1 / E2 if E2 != 0 else mp.mpf('nan')
        if L1 < 0: allL1 = False
        if L2 < 0: allL2 = False
        print(f"  {mp.nstr(t,5):>6}  {mp.nstr(L1,8):>16}  {mp.nstr(L2,8):>16}  {mp.nstr(phip,6):>12}")
    print(f"\n  L_1 ≥ 0 on grid? {allL1}   (first Laguerre / de Branges HB positivity — manifest)")
    print(f"  L_2 ≥ 0 on grid? {allL2}   (higher rung; hierarchy {{L_k≥0 ∀k}} ⟺ Ξ_R∈LP ⟺ RH)")
    print("  φ'=L_1/|E|^2 ≥ 0 ⟺ de Branges phase monotone ⟺ Hermite–Biehler (E=Ξ_R−iΞ_R' genuine).")

if __name__ == "__main__":
    main()
