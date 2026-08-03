# Corpus now owns a sieve: Brun's pure sieve on an integer interval

Before 2026-08-03 the corpus had **no sieve at all** and mathlib's `Mathlib/NumberTheory/SelbergSieve.lean`
stops at the diagonalized Λ² quadratic form (`mainSum_lambdaSquared_eq_sum_mul_sum_sq`) — no optimized
level, no fundamental lemma, no Brun–Titchmarsh. mathlib also has **no** Bonferroni inequality.

## What exists now — `formal/GaloisForLFunctions/RHTower/Sieve/`

All in namespace `RHTower.Sieve`, all unconditional (`propext, Classical.choice, Quot.sound` only),
all wired into `GaloisForLFunctions/RHTower.lean`.

- `IntervalMultiples.lean`
  - `card_filter_dvd_Ioc (d a b) (hab : a ≤ b) : #{x ∈ Ioc a b | d ∣ x} = b/d - a/d`
  - `abs_card_filter_dvd_Ioc_sub_lt` : `|count − ((b:ℝ)−a)/d| < 1` (the sieve remainder `R_d`)
- `TruncatedMoebius.lean`
  - `alternating_choose_partialSum k r : ∑_{j≤r} (−1)^j C(k+1,j) = (−1)^r C(k,r)`
  - `sum_divisors_filter_card_primeFactors_le` : squarefree divisor ↔ powerset transfer (filtered)
  - `sum_divisors_moebius_filter_card_le` : exact truncated value `(−1)^r C(ω m − 1, r)`
  - `indicator_le_sum_divisors_moebius_filter_card_le` (even r), and the odd mirror — Bonferroni
- `BrunPure.lean`
  - `truncDivisors m r := {d ∈ m.divisors | #d.primeFactors ≤ r}`
  - `card_coprime_Ioc_le` / `le_card_coprime_Ioc` — the sieve with main term
    `(b−a) ∑_{d∈truncDivisors} μ d/d` and error `#truncDivisors m r`
  - `coprime_prod_primes_iff`
- `MainTerm.lean`
  - `sum_divisors_eq_sum_powerset` (unfiltered transfer)
  - `sum_divisors_moebius_div_eq_prod` : `∑_{d∣m} μ d/d = ∏_{p∣m}(1−1/p)`
  - `card_truncDivisors` : `= ∑_{j≤r} C(ω m, j)`
- `TruncationDefect.lean`
  - `sum_divisors_pow_card_primeFactors_div_eq_prod` : `∑_{d∣m} λ^{ω d}/d = ∏_{p∣m}(1+λ/p)`
  - `abs_sum_truncDivisors_moebius_div_sub_prod_le` : defect `≤ λ^{−r} ∏(1+λ/p)`
  - **capstones** `card_coprime_Ioc_le_prod` (even r) / `prod_sub_le_card_coprime_Ioc` (odd r)

## The one idea that made stage 4 cheap

Do **not** formalize `j! · e_j ≤ S^j` (Maclaurin / elementary symmetric functions). Instead tilt:
every discarded divisor has `ω d > r`, so `λ^r/d ≤ λ^{ω d}/d` for `λ ≥ 1`, and
`∑_{d∣m} λ^{ω d}/d = ∏_{p∣m}(1+λ/p)` is one `Finset.prod_add`. Optimizing `λ ≍ r/∑_{p∣m}1/p`
gives the same geometric decay as the classical fundamental lemma. No factorials, no symmetric
function theory, no Newton identities.

## Traps hit

- `μ` notation needs `open scoped ArithmeticFunction.Moebius` (NOT `ArithmeticFunction`).
- `Finset.sum_boole` did not resolve; use `Finset.natCast_card_filter (p) (s)` instead.
- `Nat.mul_div_le'` and `Nat.lt_div_add_one_mul_self` do not exist; get both floor bounds from
  `Nat.div_add_mod` + `Nat.mod_lt` + `omega`.
- `div_le_div_of_nonneg_right` has a different signature here; go through
  `div_eq_mul_inv` + `mul_le_mul_of_nonneg_right`.

## Why it was built

Owner card `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/route-e-two-sided-off-normal-wold-breadth-transport.md`
needs Shiu's short-interval bound for `z^{ω(n)}` (its equation (6)). Stages left there: `Shiu.lean`,
then `(7)`–`(9)`. The same sieve also supplies Brun–Titchmarsh, which
`route-e-reciprocal-marker-mobius-hall-law.md` (26) needs.
