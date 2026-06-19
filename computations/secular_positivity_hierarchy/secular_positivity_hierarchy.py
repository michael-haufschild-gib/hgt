#!/usr/bin/env python3.13
"""
The secular positivity hierarchy: one tower of RH-equivalent positivities on the same
Newton-equivalent secular data, welding the team's pieces (Pk, li, turan) with the
Toeplitz/Pólya-frequency face.

Bases (all Newton-equivalent):
  a_j   = [s^j](zeta'/zeta)(0)          (prime side; a_0 = log 2pi)
  P_k   = sum_rho rho^{-k} = 1 - (-1)^k zeta(k)/2^k - a_{k-1}   (origin power sums; secular_moments_Pk)
  p_j   = sum_{gamma>0} gamma^{-2j} = secondzeta(2j)            (centered power sums of x_k=1/gamma_k^2)
  e_n   = elementary symmetric of {1/gamma_k^2}                 (Newton <- p_j)
  c_n   = xi(1/2) * e_n = [w^n] Xi(sqrt w)                      (Toeplitz/PF coefficients)

Hierarchy rungs (each RH-equivalent positivity, all on this data):
  Rung 1 (linear):       Li     lambda_n >= 0,  lambda_n = nP1+(1-n)+Z_n-A_n,  Z_n arch(+) vs A_n prime
  Rung 2 (quadratic):    Turan  c_n^2 - c_{n-1}c_{n+1} >= 0          (CNV, free)
  Rung 3 (determinant):  Jensen disc(J_{3,n}) >= 0                   (GORZ, free for n large)
  uniform-d:             total positivity = Lambda <= 0 = RH

Tests:
 (1) Newton duality cross-check: e_n from power sums (secondzeta) MUST equal c_n/xi(1/2) from
     the independent contour-Taylor of Xi(sqrt w). (Certifies Hankel<->Toeplitz Newton-duality.)
 (2) Rung 1 (Li) with the archimedean/prime split Z_n vs A_n and the margin.
 (3) Rungs 2,3 (Turan, Jensen) margins on the genuine c_n.
"""
import mpmath as mp

mp.mp.dps = 40

def xi(s):
    return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)

def esymm_from_power(P, Nmax):
    # Newton's identities: e_0=1, n e_n = sum_{i=1}^n (-1)^{i-1} e_{n-i} p_i
    e = [mp.mpf(1)]
    for n in range(1, Nmax+1):
        s = mp.mpf(0)
        for i in range(1, n+1):
            s += (-1)**(i-1) * e[n-i] * P[i]
        e.append(s/n)
    return e

def true_c(M, radius):
    g = lambda z: xi(mp.mpf('0.5') + z)
    tc = mp.taylor(g, mp.mpf(0), 2*M, method='quad', radius=radius)
    return [mp.re(tc[2*n]) for n in range(M+1)]

def main():
    M = 12
    print(f"=== secular positivity hierarchy (dps={mp.mp.dps}) ===")
    # power sums p_j = secondzeta(2j)
    P = [None] + [mp.secondzeta(2*j) for j in range(1, M+1)]
    print(f"  p_1 = secondzeta(2) = {mp.nstr(P[1],14)}  (= e_1 = c_1/c_0)")
    e = esymm_from_power(P, M)
    xih = mp.re(xi(mp.mpf('0.5')))
    c_newton = [xih*en for en in e]
    c_contour = true_c(M, mp.mpf(3))

    print("\n=== (1) Newton duality: e_n from power sums (secondzeta) vs contour-Taylor c_n ===")
    worst = mp.mpf(0)
    for n in range(0, 9):
        rel = abs(c_newton[n]-c_contour[n])/abs(c_contour[n])
        worst = max(worst, rel)
        print(f"  n={n}: c_Newton={mp.nstr(c_newton[n],11)}  c_contour={mp.nstr(c_contour[n],11)}  rel.diff={mp.nstr(rel,4)}")
    print(f"  worst rel.diff (n<=8) = {mp.nstr(worst,4)}  (small => Hankel<->Toeplitz Newton-duality certified)")

    print("\n=== (2) Rung 1 (Li): lambda_n = nP1+(1-n)+Z_n-A_n;  Z_n archimedean(+), A_n prime ===")
    f = lambda s: mp.zeta(s, 1, 1)/mp.zeta(s)
    a = mp.taylor(f, 0, M+2)
    P1 = 1 + mp.euler/2 - mp.log(4*mp.pi)/2
    print(f"  a_0={mp.nstr(a[0],12)} (=log2pi)   P_1={mp.nstr(P1,12)} (=1+gamma_E/2-log(4pi)/2)")
    for n in range(1, 9):
        Zn = sum(mp.binomial(n, j)*mp.zeta(j)/mp.mpf(2)**j for j in range(2, n+1))
        An = sum(mp.binomial(n, j)*(-1)**(j+1)*a[j-1] for j in range(2, n+1))
        lam = n*P1 + (1-n) + Zn - An
        marg = (Zn-An)/Zn if Zn != 0 else mp.mpf('nan')
        print(f"  n={n}: lambda={mp.nstr(lam,9)} (>=0)  Z={mp.nstr(Zn,7)}  A={mp.nstr(An,7)}  (Z-A)/Z={mp.nstr(marg,6)}")

    print("\n=== (3) Rungs 2,3 (Turan, Jensen) margins on genuine c_n ===")
    c = c_contour
    for n in range(1, M-2):
        m2 = c[n]**2/(c[n-1]*c[n+1]) - 1
        a0, a1, a2, a3 = c[n], 3*c[n+1], 3*c[n+2], c[n+3]
        d3 = 18*a3*a2*a1*a0 - 4*a2**3*a0 + a2**2*a1**2 - 4*a3*a1**3 - 27*a3**2*a0**2
        print(f"  n={n:2d}: Turan margin={mp.nstr(m2,6)} (>=0)   Jensen J3 disc {'>=0' if d3>=0 else '<0'}")

    print("\n# The four bases are one object (Newton); each rung is an RH-equivalent positivity on it;")
    print("# the uniform-d top of the tower = total positivity = Lambda<=0 = RH (the no-margin limit).")

if __name__ == "__main__":
    main()
