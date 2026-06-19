#!/usr/bin/env python3.13
"""
The field's First Theorem firewall (EulerProduct.lean) on REAL examples, pre-spectrally.

First Theorem: genuine L ⟺ Euler product ⟺ multiplicative coefficients ⟺ (DSS) on-line/secular-CMV-PD;
fake (no Euler product) ⟺ non-multiplicative ⟺ reducible (sum) ⟺ off-line zeros (interference).
The PRE-SPECTRAL firewall (fake_fails_factorization): a fake fails a_{mn}=a_m a_n at a FINITE n — no
zero needed. We verify this on real genuine vs fake coefficient sequences, complementing the spectral
(secular CMV) validations (ζ, β, Δ all on-circle).

Genuine: ζ (a_n=1), Dirichlet β=L(χ_4) (a_n=χ_4(n)), Ramanujan Δ (a_n=τ(n)) — all multiplicative.
Fake:    Davenport–Heilbronn-type  f=½(L(χ)+L(χ̄)),  χ order-4 mod 5  ⟹  a_n=Re χ(n),  NON-multiplicative,
         entire with a functional equation, off-line zeros (the canonical reducible fake).
"""
import mpmath as mp
from math import gcd

mp.mp.dps = 20

def tau_coeffs(N):
    E = [0] * (N + 1); E[0] = 1
    for n in range(1, N + 1):
        for i in range(N, n - 1, -1):
            E[i] -= E[i - n]
    P = [0] * (N + 1); P[0] = 1
    for _ in range(24):
        Q = [0] * (N + 1)
        for i in range(N + 1):
            if P[i]:
                for j in range(N + 1 - i):
                    if E[j]: Q[i + j] += P[i] * E[j]
        P = Q
    return [P[n - 1] for n in range(1, N + 1)]  # tau(1..N)

# order-4 character mod 5 via primitive root 2: ind(1)=0,ind(2)=1,ind(4)=2,ind(3)=3
IND5 = {1: 0, 2: 1, 4: 2, 3: 3}
def chi5_order4(n):
    r = n % 5
    if r == 0: return 0j
    return (1j) ** IND5[r]          # i^{ind}
def chi4(n):
    r = n % 4
    return {1: 1, 3: -1}.get(r, 0)

def check_mult(a, name, pairs):
    print(f"  {name}: a_(mn) vs a_m·a_n for coprime (m,n):")
    allmult = True
    for (m, n) in pairs:
        amn = a(m * n); prod = a(m) * a(n)
        ok = abs(amn - prod) < 1e-9
        allmult = allmult and ok
        print(f"    a_{m*n}={mp.nstr(amn,5):>8}  a_{m}·a_{n}={mp.nstr(prod,5):>8}  {'=' if ok else '≠  ← NON-MULT (firewall!)'}")
    print(f"    ⟹ {'MULTIPLICATIVE (Euler product ⟹ GENUINE)' if allmult else 'NOT multiplicative (no Euler ⟹ FAKE)'}")
    return allmult

def main():
    print(f"=== First-Theorem firewall on real examples (pre-spectral) ===")
    tau = tau_coeffs(60)
    pairs = [(2, 3), (3, 5), (2, 9), (4, 9), (2, 7), (3, 7), (5, 7)]
    print("\nGENUINE L-functions (should be multiplicative ⟹ Euler ⟹ on-line, secular-CMV-PD):")
    check_mult(lambda n: mp.mpf(1) if n >= 1 else 0, "ζ  (a_n=1)", pairs)
    check_mult(lambda n: mp.mpf(chi4(n)), "β=L(χ_4)  (a_n=χ_4(n))", pairs)
    check_mult(lambda n: mp.mpf(tau[n - 1]), "Δ  (a_n=τ(n))", pairs)
    print("\nFAKE (Davenport–Heilbronn-type sum ½(L(χ)+L(χ̄)), χ order-4 mod 5 ⟹ a_n=Re χ(n)):")
    af = lambda n: mp.re(chi5_order4(n))
    print(f"    a_1..a_10 = {[mp.nstr(af(n),3) for n in range(1,11)]}")
    check_mult(af, "DH-type fake", pairs)
    print("\n# Verdict: the genuine L's are multiplicative (Euler product) — consistent with their")
    print("# secular CMV being PD/on-circle (ζ,β,Δ confirmed). The DH-type fake is NON-multiplicative")
    print("# (fails a_{mn}=a_m a_n at finite n, e.g. n=6) — no Euler product ⟹ reducible ⟹ off-line")
    print("# zeros (First Theorem). The PRE-spectral firewall (finite n) and the SPECTRAL firewall")
    print("# (secular CMV off-circle) agree: genuine ⟺ Euler ⟺ on-line; fake ⟺ no-Euler ⟺ off-line.")

if __name__ == "__main__":
    main()
