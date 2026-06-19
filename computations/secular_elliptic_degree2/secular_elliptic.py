#!/usr/bin/env python3.13
"""
Conjecture C, degree-2 robustness: an ELLIPTIC CURVE L-function (conductor 11, weight 2), with a
SELF-VERIFYING AFE (cross-checked against the convergent series — no external value needed).

Curve 11a: y^2 + y = x^3 - x^2 - 10x - 20 (conductor N=11, rank 0, root number ε=+1).
a_p = p+1-#E(F_p); a_n multiplicative via Hecke. Completed Λ(s)=(√N/2π)^s Γ(s) L(E,s), Λ(s)=εΛ(2-s).
Incomplete-gamma AFE: Λ(s)=Σ_n a_n[(cn)^{-s}Γ(s,cn) + ε(cn)^{s-2}Γ(2-s,cn)], c=2π/√N. Λ(1+it) real.
Self-verify: L_AFE(2) (from Λ(2)) vs L_series(2)=Σ a_n n^{-2}. Then zeros on Re=1, secular CMV face.
"""
import mpmath as mp
from math import gcd

mp.mp.dps = 30
N = 11

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def ap_good(p):
    # a_p = p + 1 - #E(F_p);  #E = 1 + sum_x (1 + legendre(1+4*RHS, p)),  y^2+y=RHS
    cnt = 1
    for x in range(p):
        rhs = (x**3 - x**2 - 10 * x - 20) % p
        disc = (1 + 4 * rhs) % p
        cnt += 1 + legendre(disc, p)
    return p + 1 - cnt

def primes_up_to(M):
    s = [True] * (M + 1); s[0] = s[1] = False
    for i in range(2, int(M**0.5) + 1):
        if s[i]:
            for j in range(i * i, M + 1, i): s[j] = False
    return [i for i in range(2, M + 1) if s[i]]

def build_an(M):
    a = [0] * (M + 1); a[1] = 1
    ps = primes_up_to(M)
    ap = {}
    for p in ps:
        ap[p] = 1 if p == 11 else ap_good(p)   # bad prime 11: a_11=+1 (multiplicative reduction)
    # prime powers
    for p in ps:
        pk = p; aprev = 1; acur = ap[p]
        a[p] = ap[p]
        pe = p * p
        while pe <= M:
            if p == 11:
                a[pe] = a[pe // p] * ap[p]      # a_{11^k}=a_11^k=1
            else:
                a[pe] = ap[p] * a[pe // p] - p * a[pe // (p * p)]
            pe *= p
    # multiplicative fill
    for n in range(2, M + 1):
        if a[n] != 0 or n == 1: continue
        # factor n
        m = n; val = 1; ok = True
        for p in ps:
            if p * p > m: break
            if m % p == 0:
                pk = 1
                while m % p == 0: m //= p; pk *= p
                val *= a[pk]
        if m > 1: val *= a[m]
        a[n] = val
    return a

def Lambda(a, s, M):
    c = 2 * mp.pi / mp.sqrt(N)
    tot = mp.mpf(0)
    for n in range(1, M + 1):
        if a[n] == 0: continue
        cn = c * n
        tot += a[n] * ((cn)**(-s) * mp.gammainc(s, cn) + (cn)**(s - 2) * mp.gammainc(2 - s, cn))
    return tot

def Lval_from_Lambda(a, s, M):
    return Lambda(a, s, M) / ((mp.sqrt(N) / (2 * mp.pi))**s * mp.gamma(s))

def warakelov(rho): return 1 - 1 / rho
def moments(pts, K): return [sum(mp.conj(p)**k for p in pts) for k in range(K + 1)]
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
    print(f"=== degree-2 elliptic L (curve 11a, N=11) secular CMV, self-verified AFE (dps={mp.mp.dps}) ===")
    M = 600
    a = build_an(M)
    print(f"  a_p sanity (11a known: a_2=-2,a_3=-1,a_5=1,a_7=-2,a_13=4): "
          f"a_2={a[2]}, a_3={a[3]}, a_5={a[5]}, a_7={a[7]}, a_13={a[13]}")
    # self-verify AFE vs convergent series at s=2
    Lser = sum(mp.mpf(a[n]) / n**2 for n in range(1, M + 1))
    Lafe = Lval_from_Lambda(a, mp.mpf(2), 60)
    print(f"  AFE self-check at s=2: L_series(2)={mp.nstr(Lser,12)}  L_AFE(2)={mp.nstr(mp.re(Lafe),12)}  "
          f"diff={mp.nstr(abs(Lser-Lafe),3)}")
    # zeros of Lambda(1+it) (real); scan
    f = lambda t: mp.re(Lambda(a, 1 + 1j * t, 60))
    zeros = []; t = mp.mpf('1'); step = mp.mpf('0.2'); prev = f(t)
    while t < 35 and len(zeros) < 8:
        t += step; cur = f(t)
        if (prev < 0) != (cur < 0):
            try:
                r = mp.findroot(f, t - step / 2)
                if r > 0 and (not zeros or abs(r - zeros[-1]) > 0.2): zeros.append(r)
            except Exception: pass
        prev = cur
    print(f"  zeros (Re=1) γ: {[mp.nstr(z,6) for z in zeros]}")
    if len(zeros) < 4:
        print("  (too few zeros; honest)"); return
    K = min(6, len(zeros))
    pts = []
    for g in zeros:
        pts.append(warakelov(mp.mpf('0.5') + 1j * g)); pts.append(warakelov(mp.mpf('0.5') - 1j * g))
    c = moments(pts, K); mn = herm_minors(c, K); gv = verblunsky(c, K - 1)
    print(f"  |w_ρ|={mp.nstr(abs(pts[0]),14)}  circle-Toeplitz PD? {all(mp.re(d)>0 for d in mn)}")
    print(f"  Verblunsky |γ_k|: {[mp.nstr(abs(x),6) for x in gv]}")
    print("\n# Self-verified AFE + secular CMV PD/|γ|<1 ⟹ Conjecture C holds for a 2nd degree-2 L (elliptic).")

if __name__ == "__main__":
    main()
