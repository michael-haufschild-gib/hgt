#!/usr/bin/env python3.13
"""
The CMV / OPUC (unitary) face of the secular hierarchy, via the Arakelov w-coordinate.

Arakelov map w_ρ = 1 - 1/ρ sends a zero ρ to the UNIT CIRCLE iff Re ρ = ½ (ArakelovW.lean:
‖w_ρ‖=1 ⟺ Re ρ=½). So {w_ρ} is a measure on the unit circle ⟺ RH. Its trigonometric moments
      c_k = Σ_ρ \bar{w_ρ}^k        (Hermitian Toeplitz: c_{-k}=conj c_k)
form a HERMITIAN TOEPLITZ matrix T=[c_{i-j}]. Trigonometric moment problem:
      T ⪰ 0  ⟺  the moments come from a positive measure ON the circle  ⟺  all w_ρ on |w|=1  ⟺  RH.
Equivalently the Verblunsky/reflection coefficients (Schur–Levinson) satisfy |γ_k| < 1 ⟺ T PD.
This is the UNITARY (OPUC/CMV) analog of the Hermitian (OPRL/Jacobi, Hankel) face — well-conditioned
(nodes spread on the circle, no 1/γ² clustering), and welds ArakelovW to the operator picture.
The integrable flow here is the Schur/Ablowitz–Ladik flow (the circle analog of Toda).

Tests: (1) genuine (on-circle) ⟹ T PD (leading minors>0) and |γ_k|<1 (secular CMV unitary);
       (2) push a zero off-line ⟹ w off the circle ⟹ T loses PD / |γ_k|≥1 (off-line detected).
"""
import mpmath as mp

mp.mp.dps = 40
K = 10

def moments(points, K):
    # c_k = Σ_i conj(point_i)^k ; Hermitian: c_{-k}=conj(c_k)
    return [sum(mp.conj(p)**k for p in points) for k in range(K + 1)]

def herm_toeplitz_leading_minors(c, K):
    def entry(i, j):
        k = i - j
        return c[k] if k >= 0 else mp.conj(c[-k])
    minors = []
    for n in range(1, K + 1):
        M = mp.matrix([[entry(i, j) for j in range(n)] for i in range(n)])
        minors.append(mp.det(M))
    return minors

def levinson_reflection(c, K):
    # reflection coeffs γ_n for Hermitian Toeplitz; |γ_n|<1 ⟺ PD
    a = [mp.mpf(1)]
    E = mp.re(c[0])
    gammas = []
    for n in range(1, K + 1):
        acc = c[n]
        for j in range(1, n):
            acc += a[j] * c[n - j]
        gamma = -acc / E
        gammas.append(gamma)
        newa = a + [mp.mpf(0)]
        for j in range(1, n):
            newa[j] = a[j] + gamma * mp.conj(a[n - j])
        newa[n] = gamma
        a = newa
        E = E * (1 - abs(gamma)**2)
    return gammas

def warakelov(rho):
    return 1 - 1 / rho

def main():
    N = 40
    g = [mp.im(mp.zetazero(n)) for n in range(1, N + 1)]
    # genuine: points on the circle, w(½±iγ)
    pts = []
    for gi in g:
        pts.append(warakelov(mp.mpf('0.5') + mp.mpc(0, gi)))
        pts.append(warakelov(mp.mpf('0.5') - mp.mpc(0, gi)))
    print(f"=== secular CMV/OPUC via Arakelov w (N={N}, dps={mp.mp.dps}) ===")
    print(f"  sample |w_ρ| (should be 1 on RH): {mp.nstr(abs(pts[0]),20)}")
    c = moments(pts, K)
    minors = herm_toeplitz_leading_minors(c, K)
    allpos = all(mp.re(d) > 0 for d in minors)
    print("\n(1) genuine (on-circle): Hermitian Toeplitz leading minors (PD ⟺ on circle ⟺ RH)")
    print("   " + "  ".join('+' if mp.re(d) > 0 else '-' for d in minors) + f"   all>0? {allpos}")
    gammas = levinson_reflection(c, K - 1)
    print("   Verblunsky/reflection |γ_k| (PD ⟺ all <1):")
    for k, gk in enumerate(gammas, 1):
        print(f"     |γ_{k}| = {mp.nstr(abs(gk),8)}  {'<1' if abs(gk) < 1 else '>=1 !'}")

    print("\n(2) push zero #1 off-line by δ -> w off the circle -> T loses PD / |γ|≥1")
    for d in ['1.0', '0.3', '0.1']:
        delta = mp.mpf(d)
        ptp = []
        ptp.append(warakelov(mp.mpf('0.5') + delta + mp.mpc(0, g[0])))
        ptp.append(warakelov(mp.mpf('0.5') + delta - mp.mpc(0, g[0])))   # conjugate partner
        ptp.append(warakelov(mp.mpf('0.5') - delta + mp.mpc(0, g[0])))   # FE partner (keeps set σ,conj-closed)
        ptp.append(warakelov(mp.mpf('0.5') - delta - mp.mpc(0, g[0])))
        for gi in g[1:]:
            ptp.append(warakelov(mp.mpf('0.5') + mp.mpc(0, gi)))
            ptp.append(warakelov(mp.mpf('0.5') - mp.mpc(0, gi)))
        cp = moments(ptp, K)
        mp_minors = herm_toeplitz_leading_minors(cp, K)
        nneg = sum(1 for dd in mp_minors if mp.re(dd) <= 0)
        gp = levinson_reflection(cp, K - 1)
        maxg = max(abs(gk) for gk in gp)
        offc = abs(abs(warakelov(mp.mpf('0.5') + delta + mp.mpc(0, g[0]))) - 1)
        print(f"  δ={d:4s}: |w|−1={mp.nstr(offc,4)}  #nonpos leading minors={nneg}  max|γ_k|={mp.nstr(maxg,6)}  "
              f"{'OFF-CIRCLE detected' if nneg > 0 or maxg >= 1 else 'still PD'}")

if __name__ == "__main__":
    main()
