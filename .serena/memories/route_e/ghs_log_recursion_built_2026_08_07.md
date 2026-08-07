# GHS log recursion is built (2026-08-07)

`RHTower/Sieve/MultiplicativeLogRecursion` + `HTGeometry/GeneralisedVonMangoldt`, both green,
axiom-clean, umbrella-wired.

Entry point: `abs_sum_Icc_mul_log_sub_sum_primes_le'` —
`|S_f(N) log N − ∑_{p ≤ N} f(p) log p S_f(⌊N/p⌋)| ≤ (9 + RHTower.Mertens.mertensTail) · N`
for bounded completely multiplicative `f`.  The only hypotheses are `f (m*n) = f m * f n` and
`|f n| ≤ 1` — the definition of the class.  Do NOT state the recursion through
`vonMangoldtOf`/`dirichletInverse`: that drags in an `Invertible (f 1)` argument for nothing, since for
completely multiplicative `f` the weight is the concrete `f·Λ`.  And do not add premises about `S_f`
itself (e.g. "ε-small at all smaller scales"): such a premise is a fact about the object, cannot be
discharged, and makes the theorem conditional.

Built entirely from assets that already existed for other purposes:
- `ArithmeticFunction.self_mul_dirichletInverse` (mathlib) gives `f·log = f * Λ_f` in three lines.
- `RHTower.sum_Icc_mul_apply` (DirichletSummatorySwap) is the hyperbola swap.
- `RHTower.Sieve.le_log_factorial` (Sieve/MertensFirst) is the log-shift cost `N log N − log N! ≤ N`.
- `RHTower.Mertens.tail_bounded` (RHTower/MertensFirst — a *different* module from
  Sieve/MertensFirst) bounds `∑_{d ≤ N, ¬prime} Λ(d)/d ≤ 8 + mertensTail`; this is exactly the
  prime-power excess of the recursion. Do not reprove it by reindexing `(p,e) ↦ p^e`.

Claims no decay, and cannot: the identity is tight for `f = 1`. Its value is that the remaining gate has
no Dirichlet polynomial of length `x` and no short-height mean-value theorem — so the three contour-route
no-gos (`halasz_route_loses_log_squared_*`, `mean_square_wrong_regime_no_go_*`) do not apply to it — and
the prime sum is *signed*, so cancellation survives. The absolute-value forms
(`abs_sum_Icc_mul_log_le`, `..._le_primes`) are strictly weaker and provably cannot give decay.

Traps hit: `N !` does not parse without `open Nat` (use `Nat.factorial N`); `abs_add` is now
`abs_add_le`; `Finset.sum_sub_distrib` is the forward splitting direction.
