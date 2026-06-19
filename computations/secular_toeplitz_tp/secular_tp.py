#!/usr/bin/env python3.13
"""
Total-positivity test for the (B) brick: RH as Toeplitz total positivity of the secular
coefficients, and the moment-vs-frequency separation that says what the FE forces.

Setup.  Xi(z) = xi(1/2 + z) is real, even, entire of order 1 (FE => even, reality => real coeffs).
With w = z^2,  F(w) = Xi(sqrt(w)) is entire of genus 0 (order 1/2) and (Hadamard, on RH)
        F(w) = xi(1/2) * prod_{gamma>0} (1 + w/gamma^2),
so its Taylor coefficients are  c_n = xi(1/2) * e_n( {1/gamma_k^2} )   (elementary symmetric).
Also  (2n)! c_n = mu_{2n} = int u^{2n} Phi(u) du  is a STIELTJES moment sequence (Polya, Phi>0).

Two classical sign-regularity faces of "all squared-zeros real negative" (= RH):
  * HANKEL of the moments mu_n  PSD   <=> (mu_n) Stieltjes      -- TRUE UNCONDITIONALLY (Phi>0).
  * TOEPLITZ of the coeffs  c_n  TP   <=> (c_n) Polya-frequency  <=> RH   (Aissen-Schoenberg-Whitney/Edrei).
The gap = "Stieltjes moment sequence" (free) vs "Polya frequency sequence" (= RH).

Tests:
 (0) machinery: a PF example (only negative roots) has all one-sided Toeplitz minors >= 0;
     a Stieltjes-but-not-PF sequence (1+4^n) has PSD Hankel yet a NEGATIVE Toeplitz minor.
 (1) genuine c_n = xi(1/2) e_n from the first L zeros; cross-check e_1 = sum 1/gamma^2.
 (2) free rungs: TP1 (c_n>0); TP2 Turan/log-concavity margins (expect ->0, no-margin);
     Stieltjes Hankel of mu_{2n} PSD (the free moment positivity).
 (3) Toeplitz TP of orders 2,3,4 on the genuine secular coefficients: min minor >= 0.
 (4) perturbation: push one zero off-line -> a Toeplitz minor goes NEGATIVE; sweep delta.
"""
import itertools
import mpmath as mp
from multiprocessing import Pool

mp.mp.dps = 60

# ---------- polynomial / sequence helpers ----------
def poly_mul(a, b):
    c = [mp.mpf(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            c[i + j] += ai * bj
    return c

def coeffs_from_negroots(bs):
    """coeffs (ascending) of prod (1 + w/b_k),  b_k > 0  -> all-negative-real-root polynomial."""
    p = [mp.mpf(1)]
    for b in bs:
        p = poly_mul(p, [mp.mpf(1), 1 / b])
    return p

def coeffs_with_one_complex_pair(bs, wprime):
    """replace the first real factor (1 + w/bs[0]) by (1 - w/wprime)(1 - w/conj(wprime))."""
    p = [mp.mpf(1)]
    quad = poly_mul([mp.mpf(1), -1 / wprime], [mp.mpf(1), -1 / mp.conj(wprime)])
    quad = [mp.re(x) for x in quad]               # real (conjugate pair)
    p = poly_mul(p, quad)
    for b in bs[1:]:
        p = poly_mul(p, [mp.mpf(1), 1 / b])
    return p

# ---------- Toeplitz total positivity (one-sided: a_k for k>=0, else 0) ----------
def toeplitz_entry(a, i, j):
    k = i - j
    return a[k] if 0 <= k < len(a) else mp.mpf(0)

def toeplitz_min_minor(a, order, span):
    """min over all order x order minors with row/col indices in [0, span]."""
    idx = range(0, min(span, len(a) - 1) + 1)
    best = None
    for rows in itertools.combinations(idx, order):
        for cols in itertools.combinations(idx, order):
            M = mp.matrix([[toeplitz_entry(a, i, j) for j in cols] for i in rows])
            d = mp.det(M)
            if best is None or d < best:
                best = d
    return best

def hankel_leading_minors(m, K):
    H = mp.matrix([[m[i + j] for j in range(K + 1)] for i in range(K + 1)])
    return [mp.det(H[:k, :k]) for k in range(1, K + 2)]

# ---------- zeros ----------
def _zero_im(n):
    return mp.im(mp.zetazero(n))

def get_gammas(N):
    with Pool(min(32, N)) as pool:
        return pool.map(_zero_im, range(1, N + 1))

# ---------- tests ----------
def unit_tests():
    print("=== (0) machinery: PF vs Stieltjes-not-PF ===")
    # PF: only negative real roots -> all Toeplitz minors >= 0
    a = coeffs_from_negroots([mp.mpf(k) for k in range(1, 8)])
    for r in (2, 3, 4):
        print(f"  PF  prod(1+w/k): min Toeplitz minor order {r} = {mp.nstr(toeplitz_min_minor(a, r, 7), 6)}  (>=0 expected)")
    # Stieltjes but not PF: a_n = 1 + 4^n = moments of (delta_1 + delta_4)
    s = [mp.mpf(1) + mp.mpf(4)**n for n in range(0, 8)]
    hlm = hankel_leading_minors(s, 3)
    print(f"  Stieltjes(1+4^n): Hankel leading minors = {[mp.nstr(x,4) for x in hlm]}  (>=0, PSD; rank 2 = #atoms)")
    neg = toeplitz_min_minor(s, 2, 6)
    print(f"  Stieltjes(1+4^n): min Toeplitz minor order 2 = {mp.nstr(neg,6)}  (<0 => NOT PF; moment+ does NOT give RH)")
    print()

def xi(s):
    return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)

def true_coeffs(M, radius):
    """true coefficients c_n = [w^n] Xi(sqrt w) = xi^{(2n)}(1/2)/(2n)!, via contour-Taylor."""
    g = lambda z: xi(mp.mpf('0.5') + z)
    tc = mp.taylor(g, mp.mpf(0), 2*M, method='quad', radius=radius)
    return [mp.re(tc[2*n]) for n in range(M+1)]

def min_minor_over_orders(a, orders, span):
    best, where = None, None
    for r in orders:
        mm = toeplitz_min_minor(a, r, span)
        if best is None or mm < best:
            best, where = mm, r
    return best, where

def main():
    unit_tests()

    M = 12
    print(f"=== (1) TRUE secular coefficients c_n = xi^(2n)(1/2)/(2n)!  (contour-Taylor) ===")
    c = true_coeffs(M, mp.mpf(3))
    print(f"  c_0 = xi(1/2)            = {mp.nstr(c[0],16)}   (expect 0.4971207781883)")
    print(f"  c_1/c_0                  = {mp.nstr(c[1]/c[0],16)}")
    print(f"  secondzeta(2)=sum 1/g^2  = {mp.nstr(mp.secondzeta(2),16)}   (Hadamard: c_1/c_0 = sum 1/gamma^2)")

    print("\n=== (2) free rungs (what the FE/arithmetic forces unconditionally) ===")
    print(f"  TP1: all c_n > 0 ?  {'YES' if all(cn > 0 for cn in c) else 'NO'}  (Polya: Phi>0)")
    print("  TP2 Turan/log-concavity  c_n^2 - c_{n-1}c_{n+1}  and scale-free margin:")
    for n in range(1, M):
        lc = c[n]**2 - c[n-1]*c[n+1]
        marg = c[n]**2/(c[n-1]*c[n+1]) - 1
        print(f"    n={n:2d}: log-concavity={mp.nstr(lc,4)} (>=0)  margin={mp.nstr(marg,4)}")
    mu = [mp.factorial(2*n) * c[n] for n in range(len(c))]   # mu_{2n} = (2n)! c_n, Stieltjes
    Kh = (len(mu) - 1) // 2
    hlm = hankel_leading_minors(mu, Kh)
    print(f"  Stieltjes/Hankel of mu_(2n)=(2n)!c_n (size {Kh+1}): leading minors all > 0 ? "
          f"{'YES' if all(x > 0 for x in hlm) else 'NO'}  (FREE moment positivity = Phi>0)")

    print("\n=== (3) Toeplitz total positivity of the TRUE secular coefficients (genuine = RH-consistent) ===")
    for r in (2, 3, 4):
        mm = toeplitz_min_minor(c, r, min(M, 9))
        print(f"  min Toeplitz minor order {r} = {mp.nstr(mm,6)}  (>=0 => TP_{r} holds)")

    print("\n=== (4) perturbation: push one zero strongly off-line -> Toeplitz TP must break ===")
    Lp = 7
    gp = get_gammas(Lp)
    bs = [g**2 for g in gp]
    base = coeffs_from_negroots(bs)
    mmb, rb = min_minor_over_orders(base, (2,3,4,5,6), Lp)
    print(f"  genuine deg-{Lp} product (all real-negative roots): min minor over orders 2..6 = {mp.nstr(mmb,5)} (order {rb}; >=0 => PF/TP)")
    print("  off-line displacement delta (zero #1), most-negative Toeplitz minor over orders 2..6:")
    for d in ['12.0', '6.0', '2.0', '0.5', '0.1']:
        wprime = (mp.mpf(d) + mp.mpc(0, gp[0]))**2
        cp = coeffs_with_one_complex_pair(bs, wprime)
        roots = mp.polyroots(list(reversed(cp)), maxsteps=200, extraprec=200)
        ncomplex = sum(1 for r in roots if abs(mp.im(r)) > mp.mpf('1e-12'))
        mm, r = min_minor_over_orders(cp, (2,3,4,5,6), Lp)
        print(f"    delta={d:5s}: #complex roots={ncomplex:2d}  most-neg minor={mp.nstr(mm,5)} (order {r})  {'TP BROKEN' if mm < 0 else 'still >=0'}")

if __name__ == "__main__":
    main()
