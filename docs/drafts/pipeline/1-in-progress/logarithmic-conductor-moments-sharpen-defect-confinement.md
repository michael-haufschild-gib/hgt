# Logarithmic conductor moments sharpen defect confinement

- **ID:** logarithmic-conductor-defect-confinement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For each `η>0`, a constant `Cη` gives approximation error at most `η` by conductors `m≤exp(Cη(K+1))` for every unit vector of prime defect at most `K`, uniformly in the horizon.

## Purpose

An exponential cutoff would match the known defect-only obstruction. Combined with a logarithmic defect bound for actual negative complete-Weil eigenvectors, it would give a polynomial conductor range. That signed bound remains unproved.

## Proposed mechanism — not yet verified

1. Condition on the primes below `P`, with `log P` proportional to `(K+1)/η`. The existing rough-fibre estimate pays the conditioning error.
2. Truncate the smooth part at `A`. The existing summed valuation moment bounds its discarded mass by `2(K+ladderConstant(P))/log A`.
3. Expand the resulting gcd profile in its finite Ramanujan basis. Seek the spectral moment bound
   `Σ log(m) a_m² ≤ 2(log A+ladderConstant(P)) Σ a_m²`.
   The proposed proof bounds its actual prime defect before taking the fixed-period harmonic limit. Prime powers outside the retained prime set act trivially.
4. Compare finite-horizon smooth-part weights with the geometric valuation distribution. The proposed upper comparison uses a smooth-factor cutoff retaining half of the Euler-product harmonic mass; the lower comparison on `a≤A` uses `N≥A²`.
5. Discard conductor coefficients above `R` using the spectral moment, rather than retaining all divisors of the valuation-box modulus. Cover smaller horizons by the complete finite Ramanujan basis.

The spectral moment, quantitative measure comparison, and final exponential cutoff are open Lean obligations. This card asserts no new proved result.
