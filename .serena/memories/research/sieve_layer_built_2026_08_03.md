# Corpus owns a sieve AND Mertens' theorems (2026-08-03)

Before this date the corpus had **no sieve and no Mertens estimate**, and neither does mathlib:
`Mathlib/NumberTheory/SelbergSieve.lean` stops at the diagonalized Λ² quadratic form
(`mainSum_lambdaSquared_eq_sum_mul_sum_sq`) — no optimized level, no fundamental lemma, no
Brun–Titchmarsh; mathlib has **no** Bonferroni inequality and **no** Mertens theorem
(`rg -il mertens` over mathlib hits only `RingTheory/Polynomial/ContentIdeal.lean`).
The corpus's many `Mertens`-named modules are about `M(x)=∑μ(n)`, not `∑_{p≤x} 1/p`.

## What exists now — `formal/GaloisForLFunctions/RHTower/Sieve/`

Namespace `RHTower.Sieve`. All unconditional (`propext, Classical.choice, Quot.sound` only),
all wired into `GaloisForLFunctions/RHTower.lean`, all built.

### Sieve core
- `IntervalMultiples.lean` — `card_filter_dvd_Ioc`, `abs_card_filter_dvd_Ioc_sub_lt`
  (`|#multiples − (b−a)/d| < 1`), `cast_div_bounds` (floor sandwich, reused everywhere).
- `TruncatedMoebius.lean` — `alternating_choose_partialSum`,
  `sum_divisors_filter_card_primeFactors_le` (squarefree divisor ↔ powerset),
  `sum_divisors_moebius_filter_card_le` (`= (−1)^r C(ω m − 1, r)`), both **Bonferroni** inequalities.
- `BrunPure.lean` — `truncDivisors m r`, `card_coprime_Ioc_le` / `le_card_coprime_Ioc`,
  `coprime_prod_primes_iff`.
- `MainTerm.lean` — `sum_divisors_eq_sum_powerset`, `sum_divisors_moebius_div_eq_prod`
  (`∑_{d∣m} μd/d = ∏(1−1/p)`), `card_truncDivisors`.
- `TruncationDefect.lean` — `sum_divisors_pow_card_primeFactors_div_eq_prod`
  (`∑ λ^{ω d}/d = ∏(1+λ/p)`), `abs_sum_truncDivisors_moebius_div_sub_prod_le`,
  capstones `card_coprime_Ioc_le_prod` / `prod_sub_le_card_coprime_Ioc`.

### Mertens
- `Mertens.lean` — `prod_one_sub_inv_le_exp_neg_sum`, `prod_one_add_le_exp_sum`,
  `sum_log_primesLE_le` (Chebyshev `∑_{p≤n} log p ≤ n log 4`, from `primorial_le_four_pow`),
  `primeFactors_primorial_eq`.
- `MertensFirst.lean` — `mertensFirst_upper` (`≤ log n + log 4`) and `mertensFirst_lower`
  (`≥ log n − 1 − 2·logSqTailConst`), plus `div_le_factorization_factorial`,
  `log_factorial_eq_sum_primesLE`, `log_factorial_le`, `le_log_factorial`, `summable_log_div_sq`.
- `LogLogTelescope.lean` — `log_sub_log_le` / `le_log_sub_log`, `logLog`,
  `logLogIncrementSum`, `logLogIncrementSum_le` / `le_logLogIncrementSum`, `sum_Ico_telescope`.
- `MertensSecond.lean` — `mertensA`, `mertensS`, `mertensS_eq_abel`,
  **`mertensSecond_upper` / `mertensSecond_lower`** (`= logLog N ± const`), with named constants
  `mertensFirstConst`, `mertensSecondUpperConst`, `mertensSecondLowerConst` and aliases
  `mertensS_le` / `le_mertensS`.

### Fundamental lemma
- `RoughCount.lean` — `prod_one_sub_inv_primesLE_le` (`∏(1−1/p) ≤ exp(c₀)/log z`),
  `prod_one_add_primesLE_le` (`∏(1+λ/p) ≤ exp(λc₁)(log z)^λ`), `coprime_primorial_iff`, and
  **`card_rough_Ioc_le`**:
  `#{n ∈ (a,b] : P⁻(n) > z} ≤ (b−a)exp(c₀)/log z + (b−a)exp(λc₁)(log z)^λ/λ^r + #{d ∣ z# : ω d ≤ r}`.

## Three ideas that made this cheap

1. **Truncation tail by exponential tilt, not Maclaurin.** Discarded divisors have `ω d > r`, so
   `λ^r/d ≤ λ^{ω d}/d` and `∑_{d∣m} λ^{ω d}/d = ∏(1+λ/p)` is one `Finset.prod_add`. No `j! e_j ≤ S^j`.
2. **No Stirling.** Mertens I needs only `n^n e^{−n} ≤ n! ≤ n^n`; the lower half is one term of
   `Real.sum_le_exp_of_nonneg`.
3. **No integral comparison in Mertens II.** Concavity `(b−a)/b ≤ log b − log a ≤ (b−a)/a`
   sandwiches each term of `∑ (log(i+1)−log i)/log(i+1)` between consecutive increments of
   `log ∘ log`; the sum telescopes. Abel summation is `Finset.sum_range_by_parts`.

Sharpness matters: the leading constant in Mertens II must be exactly `1`, else the Chernoff
exponent downstream becomes `−I(c) + c log A`.

## Traps hit

- `μ` needs `open scoped ArithmeticFunction.Moebius` (NOT `ArithmeticFunction`).
- `Finset.sum_boole` does not resolve; use `Finset.natCast_card_filter (p) (s)`.
- `primorial`, `primorial_le_four_pow`, `squarefree_primorial`, `primeFactors_primorial`,
  `primorial_eq_prod_primesLE` are **root-level**, not under `Nat.`.
- Legendre lemmas are `Nat.factorization_factorial`, `Nat.factorization_factorial_le_div_pred`
  (namespace `Nat`, not `Nat.Prime`).
- `sum_le_tsum` is `Summable.sum_le_tsum` (receiver form).
- `Real.log_prod` takes only the nonvanishing hypothesis.
- State results in terms of `logLog`, not unfolded `Real.log (Real.log _)` — `linarith` then keeps
  the atoms aligned. Write `2 * (C / log 2)`, not `2 * C / log 2`, for the same reason.

## Why it was built / what is left

Owner card:
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/route-e-two-sided-off-normal-wold-breadth-transport.md`.
It needs Shiu's short-interval bound for `z^{ω(n)}` (its `(6)`). Left: smooth/rough factorization
`n = d·m`, `ω m ≤ L` for `z`-rough `m ≤ 2X` with `z = X^{1/L}`, the smooth sum
`∑_{d z-smooth} z₀^{ω d}/d ≤ ∏_{p≤z}(1 + z₀/p + z₀/p² + …)`, parameters `log z ≍ log X/log log X`,
`r ≍ log log z`; then `(7)`–`(9)`.
The same sieve supplies Brun–Titchmarsh for `route-e-reciprocal-marker-mobius-hall-law.md` `(26)`.
