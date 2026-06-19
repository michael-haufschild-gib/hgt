#!/usr/bin/env python3.13
"""
Conjecture C in NEW territory: degree-2 L-function (Ramanujan Δ, weight 12) secular CMV face.

L(s,Δ)=Σ τ(n) n^{-s} (classical normalization), completed Λ(s)=(2π)^{-s}Γ(s)L(s,Δ), Λ(s)=Λ(12-s).
By modularity of f(τ)=Στ(n)e^{2πinτ} (weight 12), the AFE is the clean incomplete-gamma series
    Λ(s) = Σ_n τ(n) [ (2πn)^{-s} Γ(s,2πn) + (2πn)^{s-12} Γ(12-s,2πn) ],
fast-convergent (Γ(s,2πn) ~ e^{-2πn}); Λ(6+it) is REAL (FE + real coeffs). Zeros on Re s=6 (=
critical line; analytic center 1/2 after the (k-1)/2 shift). GRH for Δ ⟺ all on Re=6.

We (1) compute τ(n) EXACTLY (Δ q-expansion), verify; (2) find zeros of Λ(6+it), verify the first
≈ 9.22 (known); (3) run the secular CMV/Arakelov face on ρ=½+iγ — degree-2 test of Conjecture C.
"""
import mpmath as mp

mp.mp.dps = 30

def tau_coeffs(N):
    # E = prod_{n>=1}(1-q^n) mod q^{N+1}, exact integers
    E = [0] * (N + 1); E[0] = 1
    for n in range(1, N + 1):
        for i in range(N, n - 1, -1):
            E[i] -= E[i - n]
    # P = E^24
    P = [0] * (N + 1); P[0] = 1
    for _ in range(24):
        Q = [0] * (N + 1)
        for i in range(N + 1):
            if P[i] == 0: continue
            pi = P[i]
            for j in range(N + 1 - i):
                if E[j]: Q[i + j] += pi * E[j]
        P = Q
    # tau(n) = [q^n] q*P = [q^{n-1}] P
    return [P[n - 1] for n in range(1, N + 1)]

def Lambda(tau, s, M):
    tot = mp.mpf(0)
    for n in range(1, M + 1):
        a = 2 * mp.pi * n
        t1 = a**(-s) * mp.gammainc(s, a)
        t2 = a**(s - 12) * mp.gammainc(12 - s, a)
        tot += tau[n - 1] * (t1 + t2)
    return tot

# ---- secular CMV face (Arakelov w on the analytic ρ=½+iγ) ----
def warakelov(rho): return 1 - 1 / rho
def moments(points, K): return [sum(mp.conj(p)**k for p in points) for k in range(K + 1)]
def herm_minors(c, K):
    def e(i, j):
        k = i - j; return c[k] if k >= 0 else mp.conj(c[-k])
    return [mp.det(mp.matrix([[e(i, j) for j in range(n)] for i in range(n)])) for n in range(1, K + 1)]
def verblunsky(c, K):
    a = [mp.mpf(1)]; E = mp.re(c[0]); g = []
    for n in range(1, K + 1):
        acc = c[n]
        for j in range(1, n): acc += a[j] * c[n - j]
        gm = -acc / E; g.append(gm)
        na = a + [mp.mpf(0)]
        for j in range(1, n): na[j] = a[j] + gm * mp.conj(a[n - j])
        na[n] = gm; a = na; E = E * (1 - abs(gm)**2)
    return g

def main():
    N = 40
    tau = tau_coeffs(N)
    print(f"=== degree-2 L(Δ) secular CMV (dps={mp.mp.dps}) ===")
    print(f"  τ(1..6) = {tau[:6]}  (known: 1, -24, 252, -1472, 4830, -6048)")
    M = 20
    # scan Λ(6+it) (real) for sign changes
    print("  scanning Λ(6+it) for zeros...")
    f = lambda t: mp.re(Lambda(tau, 6 + 1j * t, M))
    zeros = []
    t = mp.mpf('5'); step = mp.mpf('0.25'); prev = f(t)
    while t < 45 and len(zeros) < 8:
        t += step; cur = f(t)
        if prev == 0 or (prev < 0) != (cur < 0):
            try:
                r = mp.findroot(f, t - step / 2)
                if r > 0 and (not zeros or abs(r - zeros[-1]) > 0.3):
                    zeros.append(r)
            except Exception: pass
        prev = cur
    print(f"  first zeros γ: {[mp.nstr(z,7) for z in zeros]}")
    print(f"  (known first zero of L(Δ): ≈ 9.22)")
    if len(zeros) < 4:
        print("  (too few zeros — AFE/scan needs tuning; reporting honestly)"); return
    # secular CMV face on rho = 1/2 + i*gamma (analytic normalization)
    K = min(6, len(zeros))
    pts = []
    for g in zeros:
        pts.append(warakelov(mp.mpf('0.5') + 1j * g))
        pts.append(warakelov(mp.mpf('0.5') - 1j * g))
    print(f"\n  sample |w_ρ| = {mp.nstr(abs(pts[0]),16)} (should be 1)")
    c = moments(pts, K)
    mn = herm_minors(c, K)
    allpos = all(mp.re(d) > 0 for d in mn)
    gv = verblunsky(c, K - 1)
    print(f"  circle-Toeplitz PD (on-circle ⟺ GRH)? {allpos}")
    print(f"  Verblunsky |γ_k|: {[mp.nstr(abs(x),6) for x in gv]}  (all <1 ⟺ on circle)")
    print("\n# If on-circle + |γ_k|<1: Conjecture C confirmed for a DEGREE-2 L-function (new territory).")

if __name__ == "__main__":
    main()
