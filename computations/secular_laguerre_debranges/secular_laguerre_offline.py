#!/usr/bin/env python3.13
"""
De Branges/Laguerre FIREWALL: an off-line zero breaks a Laguerre inequality (completes §23).

A finite real-rooted Hadamard product P(t)=∏(1−t²/γ_n²) is in Laguerre-Pólya ⟹ all Laguerre
inequalities L_k≥0 (the de Branges/Hermite–Biehler positivity holds). Replace ONE real-zero pair by a
complex-conjugate pair (an off-line zero) ⟹ P is no longer real-rooted ⟹ NOT LP ⟹ some L_k(t)<0.
This validates that the de Branges/Laguerre face DISCRIMINATES RH (the firewall), like the Hankel/
Toeplitz/CMV faces.
"""
import mpmath as mp

mp.mp.dps = 30

def poly_from_realroots(gammas):
    # P(t) = prod (1 - t^2/g^2) as coefficient list (ascending, in t)
    p = [mp.mpf(1)]
    for g in gammas:
        # multiply by (1 - t^2/g^2)
        q = [mp.mpf(0)] * (len(p) + 2)
        for i, c in enumerate(p):
            q[i] += c
            q[i + 2] += -c / g**2
        p = q
    return p

def poly_with_offline(gammas, delta):
    # replace the first factor (1 - t^2/g1^2) [roots ±g1] by (1 - t/z)(1 - t/zbar), z = g1 - i*delta
    z = gammas[0] - 1j * delta
    p = [mp.mpf(1)]
    # quadratic (1 - t/z)(1 - t/zbar) = 1 - t(1/z+1/zbar) + t^2/(z*zbar); real coeffs
    b1 = -(1 / z + 1 / mp.conj(z))
    b2 = 1 / (z * mp.conj(z))
    quad = [mp.mpf(1), mp.re(b1), mp.re(b2)]
    def mul(p, f):
        q = [mp.mpf(0)] * (len(p) + len(f) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(f):
                q[i + j] += a * b
        return q
    p = mul(p, quad)
    for g in gammas[1:]:
        p = mul(p, [mp.mpf(1), mp.mpf(0), -1 / g**2])
    return p

def peval(p, t):
    return sum(c * t**i for i, c in enumerate(p))
def pder(p):
    return [i * p[i] for i in range(1, len(p))]

def laguerre(p, t):
    p1 = pder(p); p2 = pder(p1); p3 = pder(p2); p4 = pder(p3)
    f0, f1, f2 = peval(p, t), peval(p1, t), peval(p2, t)
    f3, f4 = peval(p3, t), peval(p4, t)
    L1 = f1**2 - f0 * f2
    L2 = 3 * f2**2 - 4 * f1 * f3 + f0 * f4
    return L1, L2

def main():
    L = 6
    g = [mp.im(mp.zetazero(n)) for n in range(1, L + 1)]
    print(f"=== de Branges/Laguerre firewall (L={L} zeros, dps={mp.mp.dps}) ===")
    Pg = poly_from_realroots(g)
    grid = [mp.mpf(t) for t in ['0','3','6','9','12','15','20','25','30']]
    minL1g = min(laguerre(Pg, t)[0] for t in grid)
    minL2g = min(laguerre(Pg, t)[1] for t in grid)
    print(f"  genuine (real roots): min L_1={mp.nstr(minL1g,5)}  min L_2={mp.nstr(minL2g,5)}  "
          f"{'all>=0 (LP/Hermite–Biehler)' if minL1g>=0 and minL2g>=0 else 'NEG?!'}")
    print("  off-line (zero #1 → complex pair, δ): min Laguerre over grid:")
    for d in ['3.0', '1.0', '0.3']:
        Pp = poly_with_offline(g, mp.mpf(d))
        L1s = [laguerre(Pp, t)[0] for t in grid]
        L2s = [laguerre(Pp, t)[1] for t in grid]
        mn1, mn2 = min(L1s), min(L2s)
        broke = mn1 < 0 or mn2 < 0
        print(f"    δ={d:4s}: min L_1={mp.nstr(mn1,5):>14}  min L_2={mp.nstr(mn2,5):>14}  "
              f"{'FIREWALL: Laguerre<0 ⟹ not LP ⟹ off-line detected' if broke else 'still ≥0 at this grid/order'}")
    print("\n# Off-line ⟹ some Laguerre inequality <0 ⟹ Ξ not Laguerre-Pólya ⟹ de Branges E not Hermite–Biehler.")
    print("# The de Branges/Laguerre face discriminates RH like the Hankel/Toeplitz/CMV faces (the firewall).")

if __name__ == "__main__":
    main()
