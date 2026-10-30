# Logarithmic conductor moments sharpen defect confinement

- **ID:** logarithmic-conductor-defect-confinement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For each `η>0`, a constant `Cη` gives approximation error at most `η` by conductors `m≤exp(Cη(K+1))` for every unit vector of prime defect at most `K`, uniformly in the horizon.

## Purpose

An exponential cutoff would match the known defect-only obstruction. Combined with a logarithmic defect bound for actual negative complete-Weil eigenvectors, it would give a polynomial conductor range. That signed bound remains unproved.

## Mechanism and remaining obligations

1. Condition on the primes below `P`, with `log P` proportional to `(K+1)/η`. The existing rough-fibre estimate pays the conditioning error.
2. Truncate the smooth part at `A`. The existing summed valuation moment bounds its discarded mass by `2(K+ladderConstant(P))/log A`.
3. The actual finite-sieve eigenbasis satisfies
   `Σ log(m) |⟨e_m,x⟩|² ≤ 2(log A+L_Q) ‖x‖²`
   on class vectors supported at `a≤A`; [Lean proof](../3-formalized/finite-sieve-profiles-have-logarithmic-conductor-tails.md). Positivity of the sieve operator on absolute coefficients bounds the signed prime term. The identification `e_m(a)=sqrt(sieveDensity(Q)/a)·normalizedRamanujanMode(m,a)` and total class-density mass one are also [formalized](../3-formalized/sieve-eigenbasis-is-density-weighted-ramanujan.md).
4. The geometric class density `μ_Q(a)=sieveDensity(Q)/a` has logarithmic moment at most `L_Q` and tail at most `L_Q/log T`; [Lean proof](../3-formalized/sieve-ground-mass-has-a-logarithmic-moment.md). Use a cutoff retaining half its mass and positive smooth/rough factorization to compare finite-horizon weights with `log(N+1)·μ_Q`. The lower comparison on `a≤A` uses `N≥A²`.
5. Discard conductor coefficients above `R` using the spectral moment, rather than retaining all divisors of the valuation-box modulus. Cover smaller horizons by the complete finite Ramanujan basis.

Quantitative measure comparison and the final exponential cutoff remain open Lean obligations. The spectral moment and basis identification do not yet prove finite-horizon confinement.
