"""
Regularization of the global bridge condition = Li's criterion (APEX-B), via the divisor power sums.

Note 10 / Thm 4 gave: RH <=> regularized sum_rho (beta-1/2)^2 = 0 (the DIVERGENT, equality form, axis C).
Its convergent companion on the positivity axis (B) is Li's criterion, built from the SAME divisor power
sums P_k = sum_rho rho^{-k} (the superzeta brick, Lean: superzeta_coeff_eq_powerSum):
   lambda_n = sum_rho [1 - (1 - 1/rho)^n] = sum_{j=1}^n C(n,j) (-1)^{j+1} P_j     (triangular, li_secular brick)
   Li's theorem (classical): RH  <=>  lambda_n >= 0 for all n.
So B (lambda_n >= 0, inequality) and C (sum(beta-1/2)^2 = 0, equality) are TWO power-sum readings of the
same divisor; the contour moments M_k are the common computable substrate.

This script: compute P_k and lambda_n from zeta's actual zeros, verify lambda_n > 0 (APEX-B entrance,
computed) and match known lambda_1..3. Run: python3 this.py  (~1-2 min for ~80 zeros)
"""
import mpmath as mp
mp.mp.dps = 25
half = mp.mpf(1)/2

N = 80
print(f"computing first {N} zeta zeros (pairs rho=1/2+i*gamma and conjugate)...")
gammas = [mp.zetazero(n).imag for n in range(1, N+1)]
rhos = []
for g in gammas:
    rhos.append(half + 1j*g)
    rhos.append(half - 1j*g)   # the conjugate zero (1/2 - i gamma)

def Pk(k):                      # P_k = sum_rho rho^{-k}  (centered at 0; Li/superzeta power sum)
    return mp.fsum(r**(-k) for r in rhos)

KMAX = 8
P = {k: Pk(k) for k in range(1, KMAX+1)}
print("\n  superzeta/Li power sums P_k = sum_rho rho^-k  (real parts; Im ~ 0 by conjugate symmetry):")
for k in range(1, KMAX+1):
    print(f"    P_{k} = {mp.nstr(mp.re(P[k]),8)}   (|Im| {mp.nstr(abs(mp.im(P[k])),2)})")

def lam(n):                     # lambda_n = sum_{j=1}^n C(n,j)(-1)^{j+1} P_j
    return mp.fsum(mp.binomial(n,j)*(-1)**(j+1)*P[j] for j in range(1, n+1))

print("\n  Li coefficients lambda_n = sum_{j} C(n,j)(-1)^{j+1} P_j   (RH <=> lambda_n >= 0 for all n):")
known = {1: '0.0230957', 2: '0.0923457', 3: '0.2076389'}   # classical Li values
allpos = True
for n in range(1, KMAX+1):
    ln = mp.re(lam(n))
    if ln <= 0: allpos = False
    extra = f"   (classical {known[n]})" if n in known else ""
    print(f"    lambda_{n} = {mp.nstr(ln,7)}{extra}")
print(f"\n  all lambda_n > 0 for n=1..{KMAX} (finite-zero partial sums): {allpos}")
print("  (partial sums from finite zeros approach the true lambda_n from below; positivity is the APEX-B signal.)")

print("\n  SYNTHESIS (Lemma 5): the regularization of the global bridge condition is Li's criterion.")
print("  - axis C (detection): regularized sum_rho (beta-1/2)^2 = 0   [equality; the local M_k composed]")
print("  - axis B (positivity): lambda_n = sum_j C(n,j)(-1)^{j+1} P_j >= 0  [inequality; classical Li = RH]")
print("  Both are power-sum conditions on the SAME divisor (P_k = superzeta brick); the contour moments")
print("  M_k are the common computable substrate. OPEN CORE: prove lambda_n >= 0 for ALL n (= RH = APEX-B).")
