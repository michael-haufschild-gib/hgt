"""
Check: Is B_1 = sum_p log(p)/(p-1) a convergent or divergent prime sum?
If divergent, the gamma_n = B_n*gamma + C_n factoring with finite B_n,C_n is flawed.

Also check: C_1 = -sum_p (log p)^2 * p/(p-1)^2 (the log-monomial part of the order-1 reduction)

SECRET: also compute partial sums of sum_p 1/(p*(p-1)) (Meissel-Mertens type constant) — 
to see if the related log-free density sum behaves differently.
"""
from mpmath import mp, mpf, log, euler, pi, sqrt, exp
import sympy

mp.dps = 50

# Generate primes up to P_max
P_max = 100000
primes = list(sympy.primerange(2, P_max))

# Compute partial sums of B_1 = sum_p log(p)/(p-1)
print("=== B_1 = sum_p log(p)/(p-1) partial sums ===")
partial_cutoffs = [100, 500, 1000, 5000, 10000, 50000, 99000]
B1_partial = {}
running = mpf(0)
idx = 0
for p in primes:
    running += log(mpf(p)) / (p - 1)
    if idx < len(partial_cutoffs) and p >= partial_cutoffs[idx]:
        B1_partial[partial_cutoffs[idx]] = float(running)
        print(f"  sum_{{p<={partial_cutoffs[idx]}}}: {float(running):.6f}")
        idx += 1
        if idx >= len(partial_cutoffs):
            break

print()

# Compare with Mertens' sum log(p)/p (known to diverge like log log x)
print("=== Comparison: sum_p log(p)/p partial sums (known to diverge) ===")
running2 = mpf(0)
idx = 0
partial_cutoffs2 = [100, 500, 1000, 5000, 10000]
for p in primes:
    running2 += log(mpf(p)) / p
    if idx < len(partial_cutoffs2) and p >= partial_cutoffs2[idx]:
        print(f"  sum_{{p<={partial_cutoffs2[idx]}}}: {float(running2):.6f}")
        idx += 1
        if idx >= len(partial_cutoffs2):
            break

print()

# Compute partial sums of C_1 = -sum_p (log p)^2 * p / (p-1)^2
print("=== C_1 = -sum_p (log p)^2 * p/(p-1)^2 partial sums ===")
running3 = mpf(0)
idx = 0
for p in primes[:1000]:
    running3 -= log(mpf(p))**2 * p / (p-1)**2
partial_C1 = float(running3)
print(f"  sum up to p~8000: {partial_C1:.6f}")

# Check: B_1*gamma + C_1 should give gamma_1 if the sum converges
gamma = float(euler)
gamma_1 = -0.0728158454836767248605863758749327360159  # known value
B1_up_to_99000 = float(running)
C1_check = gamma_1 - B1_up_to_99000 * gamma
print(f"\n=== Consistency check: gamma_1 = B_1*gamma + C_1 ===")
print(f"  gamma_1 = {gamma_1:.10f}")
print(f"  B_1 (partial to 99000) = {B1_up_to_99000:.6f}")
print(f"  B_1*gamma = {B1_up_to_99000 * gamma:.6f}")
print(f"  C_1 = gamma_1 - B_1*gamma = {C1_check:.6f}")
print(f"  Expected C_1 (partial) = {partial_C1:.6f}")
print(f"  Discrepancy = {abs(C1_check - partial_C1):.6f}")
print(f"  Note: if B_1 is divergent, C_1 = gamma_1 - B_1*gamma is also -inf")

print()
# SECRET MEASUREMENT: Compute sum_p 1/(p*(p-1)) — the Meissel-Mertens constant variant
# This converges (like sum 1/p^2), so we can test if it has a closed form
print("=== [EXTRA] sum_p 1/(p*(p-1)) — convergent companion ===")
running4 = mpf(0)
for p in primes:
    running4 += mpf(1) / (p * (p-1))
M_variant = float(running4)
print(f"  sum_p 1/(p*(p-1)) = {M_variant:.10f}")
# Compare to known constants
print(f"  1 - P (where P=Mertens prime product constant) ?")
# Meissel-Mertens constant M ≈ 0.2614972...
# The sum prod_p (1-1/p^2)^{-1} etc...
# For reference: sum_p 1/p(p-1) = sum_p (1/(p-1) - 1/p) = sum_p 1/(p(p-1))
# This is related to: 1 + gamma - log(4*pi)/2 - ... (Mertens related)
# Check: sum_p (1/(p-1) - 1/p) = sum_p 1/(p*(p-1))
alt = sum(mpf(1)/(p-1) - mpf(1)/p for p in primes)
print(f"  sum_p (1/(p-1) - 1/p) = {float(alt):.10f}  (should match)")
print(f"  Known: M_v ≈ 0.7731566... or differs?")
# Reference value from literature: sum_p 1/(p(p-1)) is the "Meissel-Mertens" related but distinct
print(f"  pi^2/6 - 1 = {float(pi**2/6 - 1):.10f}")
print(f"  log(2) = {float(log(2)):.10f}")

