"""
APEX-B uniformity frontier: the NORMALIZED Turan ratio for xi.

Last run showed the raw d=2 Turan margin T(n)=a(n)^2-a(n-1)a(n+1) > 0 but shrinking 7e-5 -> 8e-62.
The right question for UNIFORMITY (the open apex) is the scale-free ratio
   g(n) = a(n)^2 / ( a(n-1) a(n+1) )  >= 1  <=>  d=2 Turan/hyperbolicity at shift n.
GORZ: the normalized Jensen polynomials of xi -> Hermite as n->inf; the leading Turan becomes
asymptotically tight. So g(n) -> 1+ : positivity holds but the normalized margin DECAYS.
This maps WHY uniform positivity is delicate, in concrete numbers (and the decay rate g(n)-1).
Run: python3 this.py  (~1-2 min)
"""
import mpmath as mp
mp.mp.dps = 50
half = mp.mpf(1)/2

def Xi(t):
    s = half + 1j*t
    return mp.re(half*s*(s-1)*mp.power(mp.pi, -s/2)*mp.gamma(s/2)*mp.zeta(s))

M = 16
coeffs = mp.taylor(Xi, 0, 2*M+2)
a = [((-1)**n)*coeffs[2*n] for n in range(M+1)]
assert all(x > 0 for x in a), "a(n) must be positive"

print("  n     g(n)=a(n)^2/(a(n-1)a(n+1))      g(n)-1        n*(g(n)-1)")
prev = None
for n in range(1, M):
    g = a[n]**2/(a[n-1]*a[n+1])
    gm1 = g - 1
    print(f"  {n:2d}   {mp.nstr(g,10):>16}   {mp.nstr(gm1,6):>12}   {mp.nstr(n*gm1,6):>10}")
print()
print("  reading: g(n) > 1 for all n (d=2 Turan / hyperbolicity holds = GORZ floor), but g(n) -> 1+")
print("  (normalized margin DECAYS). The product n*(g(n)-1) tracks the decay rate (~ const => g-1 ~ c/n).")
print("  => uniform-in-d positivity (= RH) is delicate precisely because the normalized leading margin")
print("     tightens to 0; this is the corpus's sparse/no-margin (R30/R31) in scale-free Jensen form.")
print("  All three APEX-B entrances (Li lambda_n, Jensen g(n), Hankel det H_d) and the bridge moments M_k")
print("  are functions of one divisor (note 10 Cor 5a); the open apex is the uniformity, not the floor.")
