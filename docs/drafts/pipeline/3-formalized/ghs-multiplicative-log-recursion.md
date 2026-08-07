# The Granville–Harper–Soundararajan log recursion, in Lean

- **ID:** ghs-multiplicative-log-recursion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every bounded completely multiplicative `f : ArithmeticFunction ℝ` with `f 1`
  invertible,

  `|S_f(N)·log N − ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋)| ≤ (9 + mertensTail)·N`,
  where `S_f(M) = ∑_{m ≤ M} f(m)`.

  Unconditional, elementary, axiom-clean.

## Why this route

The contour route to Halász's theorem is closed by three no-gos recorded on
`halasz-programme-session-index.md`: the pointwise damped bound loses `(log N)²`, and the mean-square
repair is worse than pointwise in the regime of the application (`L ≍ x`, `T` polylog). The third no-go
named the alternative: Halász's own proof uses the *multiplicative factorisation* of `f`, never forming a
Dirichlet polynomial of length `x`. That is this card.

## The chain

| Module | Content |
|---|---|
| `HTGeometry/GeneralisedVonMangoldt` | `Λ_f := f⁻¹ * (f·log)`; the defining identity `f·log = f * Λ_f`; uniqueness; `Λ_ζ = Λ`; for completely multiplicative `f`, `Λ_f = f·Λ`, hence `|Λ_f| ≤ Λ` when `|f| ≤ 1` |
| `RHTower/Sieve/MultiplicativeLogRecursion` | the recursion, the log-shift, the prime-only reduction |

Declarations, in dependency order:

1. `pmul_log_eq_mul_vonMangoldtOf` — `f·log = f * Λ_f`, three lines from
   `ArithmeticFunction.self_mul_dirichletInverse`.
2. `eq_vonMangoldtOf_of_mul_eq` — uniqueness of the solution.
3. `pmul_log_eq_mul_pmul_vonMangoldt`, `vonMangoldtOf_eq_pmul_vonMangoldt` — for completely
   multiplicative `f` the weight is `f·Λ`: every antidiagonal term collapses by
   `f a · f b = f(ab)`, and `∑_{b ∣ n} Λ b = log n`.
4. `abs_vonMangoldtOf_le_vonMangoldt` — `|Λ_f| ≤ Λ` for `|f| ≤ 1`.
5. `sum_Icc_mul_log_eq` — **the recursion**
   `∑_{n ≤ N} f(n) log n = ∑_{d ≤ N} Λ_f(d)·S_f(⌊N/d⌋)`, by the corpus's own hyperbola swap
   `RHTower.sum_Icc_mul_apply`.
6. `sum_Icc_log_eq_log_factorial`, `abs_sum_Icc_mul_log_sub_le` — replacing the weight `log n` by
   `log N` costs `N log N − log N! ≤ N`, using the corpus's `le_log_factorial`.
7. `abs_sum_notPrimeVonMangoldt_weight_le` — **the prime-power excess is `O(N)`**: the corpus's Abel
   bound `RHTower.Mertens.tail_bounded` (`∑_{d ≤ N, d not prime} Λ(d)/d ≤ 8 + mertensTail`) applied
   termwise against the trivial divided size.
8. `abs_sum_Icc_mul_log_sub_sum_primes_le` — the signed prime-only identity.
9. `abs_sum_Icc_mul_log_sub_sum_primes_le'` — **the entry point**, the statement above.
10. `abs_sum_Icc_mul_log_le`, `abs_sum_Icc_mul_log_le_primes` — the absolute-value forms.

Everything reuses corpus assets rather than rebuilding them: the hyperbola swap, Stirling's lower bound
for `log N!`, and the Abel estimate for `ψ − θ` against the reciprocal weight were all already proved
here, in three different modules, for three other purposes.

## What it does and does not give

It does **not** give decay, and no decay is claimed. The identity is exact up to `O(N)` and is satisfied
by `f = 1`, where both sides are `≍ N log N`. Its content is a strict reduction:

* the only values of `f` that matter are the values at **primes**, with weight `log p`;
* they enter **signed**, so all cancellation is preserved (the absolute-value forms 10 are strictly
  weaker and cannot decay);
* the partial sums that appear are at the **divided scales** `⌊N/p⌋` only — no Dirichlet polynomial of
  length `N`, no mean-value theorem at a short height, hence none of the regime obstruction that closed
  the contour route.

Decay of `S_f` is now exactly equivalent to cancellation in `∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋)`, which is
where a distance hypothesis on the values `f(p)` acts. That is the next gate.

## Relation to the RH programme

Route E's dependency chain terminates at `MRBilinear`, i.e. at Matomäki–Radziwiłł, which needs Halász's
theorem as an input. This card reopens the road to Halász after the contour route was closed, so it is
upstream of the Route E wall, not a new claim about RH.
