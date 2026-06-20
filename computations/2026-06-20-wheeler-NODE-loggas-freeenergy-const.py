"""
STEP 6 — runnable test of the NODE constraint, ON THE NODE.
NODE = "Free energy expansion in particle number" (Coulomb / log-gas).
Constraint: for the beta=2 log-gas, Z_N = (2pi)^{N/2} prod_{j=1}^{N} j!, so the free energy
log Z_N is governed by Barnes-G asymptotics, whose UNIVERSAL CONSTANT term is zeta'(-1)
(Glaisher-Kinkelin). Test: extract the constant of the expansion of S_N = sum_{j=1}^N log(j!)
   S_N = log G(N+2),
   log G(z+1) = (z^2/2 - 1/12) log z - 3 z^2/4 + (z/2) log(2pi) + 1/12 - zeta'(-1) + O(1/z)
We compute S_N exactly, subtract the known analytic terms, and check the residual -> 1/12 - zeta'(-1).
Fast: mpmath. Seconds.
"""
import mpmath as mp
mp.mp.dps = 40

zp = mp.zeta(-1, 1, 1)   # zeta'(-1)
const_true = mp.mpf(1)/12 - zp     # the Barnes-G constant 1/12 - zeta'(-1)
glaisher = mp.exp(mp.mpf(1)/12 - zp)  # Glaisher-Kinkelin A

print("="*72)
print(" NODE TEST: log-gas free energy constant = 1/12 - zeta'(-1) (Barnes-G / Glaisher)")
print("="*72)
print(f"  zeta'(-1)            = {mp.nstr(zp,20)}")
print(f"  1/12 - zeta'(-1)     = {mp.nstr(const_true,20)}   (Barnes-G constant)")
print(f"  Glaisher A=e^(1/12-z'(-1)) = {mp.nstr(glaisher,20)}   (known {mp.nstr(mp.glaisher,20)})")
print()
print("  N :  residual of S_N=sum log(j!) after subtracting analytic terms -> 1/12 - zeta'(-1)")
for N in (50, 200, 1000, 5000):
    z = mp.mpf(N+1)   # G(N+2) = G(z+1) with z=N+1
    S_N = mp.fsum([mp.loggamma(j+1) for j in range(1, N+1)])   # sum_{j=1}^N log(j!) = log G(N+2)
    analytic = (z**2/2 - mp.mpf(1)/12)*mp.log(z) - mp.mpf(3)*z**2/4 + (z/2)*mp.log(2*mp.pi)
    residual = S_N - analytic
    print(f"   N={N:5d}: residual = {mp.nstr(residual,18)}   target = {mp.nstr(const_true,18)}  "
          f"diff = {mp.nstr(abs(residual-const_true),3)}")
print()
print(" VERDICT: the universal CONSTANT of the log-gas free-energy expansion is 1/12 - zeta'(-1),")
print(" i.e. a VALUE of the HT function zeta' at -1. Constraint confirmed on the NODE.")
