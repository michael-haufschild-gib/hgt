#!/usr/bin/env python3
# Verification for: per-place-source-a-gamma-carriers.md §1.
# Morita p-adic Gamma at positive integers: Gamma_p(n) = (-1)^n * prod_{0<j<n, p∤j} j.
# Claim (multiplier dichotomy #134): Gamma_p(n+1) = -n*Gamma_p(n) if p∤n, else -Gamma_p(n)
#   => polynomial multiplier -s => non-CC => Source A.  Pure integer algebra; no web search, no runpod.

def Gp(n, p):
    prod = 1
    for j in range(1, n):
        if j % p != 0:
            prod *= j
    return ((-1) ** n) * prod

print("Morita Gamma_p recurrence:  Gamma_p(n+1) = (-n if p∤n else -1) * Gamma_p(n)")
for p in [2, 3, 5, 7]:
    ok = all(Gp(n + 1, p) == ((-n) if (n % p != 0) else (-1)) * Gp(n, p) for n in range(1, 30))
    print("  p=%d : holds for n=1..29 -> %s   (multiplier -s, POLYNOMIAL = Source A by #134)" % (p, ok))
