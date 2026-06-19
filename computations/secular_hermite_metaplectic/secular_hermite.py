#!/usr/bin/env python3.13
"""
ξ in the metaplectic 𝔰𝔩₂ weight basis: the Hermite/oscillator coefficients of Ξ_R (grounds §20).

§20: the archimedean 𝔰𝔩₂ is the metaplectic algebra (X=u², Y=∂², H=u∂_u+½) and the dBN heat
generator is X. Its weight vectors are the Hermite functions h_n. So ξ's natural coordinates are
      β_n = ∫_ℝ Ξ_R(x) h_n(x) dx,   Ξ_R(x)=ξ(½+ix) (real, even),  h_n = Hermite function.
Only even n survive (Ξ_R even). We compute β_{2m}, inspect signs/decay, and the heat-flow action
(X raises weight: under H_t the weights shift), to ground the metaplectic frame with ξ's actual
oscillator-basis data. (Interpretation of Hodge–Riemann positivity in this basis is left open/honest.)
"""
import mpmath as mp

mp.mp.dps = 30

def xi(s):
    return (s * (s - 1) / 2) * mp.pi**(-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def XiR(x):
    return mp.re(xi(mp.mpf('0.5') + 1j * x))

def herm_func(n, x):
    # physicists' Hermite function h_n(x) = H_n(x) e^{-x²/2} / sqrt(2^n n! sqrt(pi))
    return mp.hermite(n, x) * mp.e**(-x**2 / 2) / mp.sqrt(mp.mpf(2)**n * mp.factorial(n) * mp.sqrt(mp.pi))

def beta(n):
    f = lambda x: XiR(x) * herm_func(n, x)
    return 2 * mp.quad(f, [0, 8, 16, 30])   # even integrand; Ξ_R decays ~ e^{-πx/4}

def main():
    print(f"=== Hermite/oscillator (metaplectic 𝔰𝔩₂ weight-basis) coefficients of Ξ_R (dps={mp.mp.dps}) ===")
    print(f"  XiR(0)=ξ(½)={mp.nstr(XiR(mp.mpf(0)),12)}")
    print("  β_{2m} = ∫ Ξ_R h_{2m} (odd vanish by evenness):")
    betas = []
    for m in range(0, 11):
        n = 2 * m
        b = beta(n)
        betas.append(b)
        print(f"    β_{n:2d} = {mp.nstr(b,10):>16}   sign {'+' if b>0 else '-' if b<0 else '0'}")
    # quick structural readout
    signs = ''.join('+' if b > 0 else '-' if b < 0 else '0' for b in betas)
    print(f"\n  sign pattern (m=0..10): {signs}")
    print("  |β_{2m}| ratios (decay):")
    for m in range(1, len(betas)):
        if betas[m-1] != 0:
            print(f"    |β_{2*m}|/|β_{2*m-2}| = {mp.nstr(abs(betas[m]/betas[m-1]),6)}")
    print("\n# Honest: this records ξ's coordinates in the metaplectic weight basis (grounding §20's 𝔰𝔩₂).")
    print("# A clean sign/positivity pattern would hint at the Hodge–Riemann structure; interpretation open.")

if __name__ == "__main__":
    main()
