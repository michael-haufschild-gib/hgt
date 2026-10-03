# U mod p per window, with the p-adic type of sigma = s(k) (full p-power or not).
import math
from valuations import smooth_upto

def trace(S, X):
    sm = smooth_upto(S, X)
    pp = sorted(set(p**a for p in S for a in range(1, 80) if p**a <= X))
    bps = sorted(set(sm) | set(pp))
    R, Q = 0, 1; j = 0; out = []
    for i, k1 in enumerate(bps):
        k2 = bps[i+1] if i + 1 < len(bps) else X + 1
        Qn = 1; av = {}
        for p in S:
            a = 0
            while p**(a+1) <= k1: a += 1
            av[p] = a; Qn *= p**a
        R = R * (Qn // Q) % Qn; Q = Qn
        while j + 1 < len(sm) and sm[j+1] <= k1: j += 1
        sigma = sm[j]
        R = (2*R + Q//sigma) % Q
        U = (R + Q//sigma) % Q
        full = {p: (sigma % p**av[p] == 0 and av[p] > 0) for p in S}
        out.append((k1, k2 - k1, sigma, {p: U % p for p in S}, full))
        U = U * pow(2, k2 - k1 - 1, Q) % Q
        R = (U - Q//sigma) % Q
    return out

for S, X in [((5, 7), 10**9), ((3, 5), 10**6)]:
    print("S =", S)
    for k1, L, sigma, res, full in trace(S, X)[:40]:
        print(f"  k1={k1:>10} L={L:>9} sigma={sigma:>10} Umod={res} full={full}")
