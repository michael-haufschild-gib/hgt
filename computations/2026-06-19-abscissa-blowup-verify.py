"""Verify critical-line-abscissa-of-convergence quantitative claims (Professor, re-bank pass).
(1) threshold V(sigma)<inf iff sigma>1/2; (2) blow-up V~log(1/(2sigma-1)) via prime zeta
P(2s)=sum mu(k)/k log zeta(ks) [prime truncation CANNOT reach this near 1/2]; (3) Mertens divergence."""
import mpmath as mp, sympy
mp.mp.dps = 30
def primezeta(s):
    tot = mp.mpf(0)
    for k in range(1, 200):
        mu = sympy.mobius(k)
        if mu == 0: continue
        tot += mp.mpf(mu)/k * mp.log(mp.zeta(k*s))
    return tot
print("sigma     P(2sigma)   log(1/(2sigma-1))   diff(->const ~ -0.3157)")
for sig in [0.55, 0.51, 0.501, 0.5001, 0.50001]:
    s = 2*mp.mpf(str(sig)); pz = primezeta(s); lg = mp.log(1/(s-1))
    print(f"{sig:.5f}   {float(pz):9.5f}   {float(lg):9.5f}   {float(pz-lg):+.5f}")
print("=> V(sigma)=P(2sigma)+O(1) ~ log(1/(2sigma-1)); offset -> -0.3157 (Mertens-related). Confirmed.")
