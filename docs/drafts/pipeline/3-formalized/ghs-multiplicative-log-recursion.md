# The Granville–Harper–Soundararajan log recursion, in Lean

- **ID:** ghs-multiplicative-log-recursion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every bounded completely multiplicative `f : ArithmeticFunction ℝ`,

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
   `∑_{n ≤ N} f(n) log n = ∑_{d ≤ N} f(d) Λ(d)·S_f(⌊N/d⌋)`, by the corpus's own hyperbola swap
   `RHTower.sum_Icc_mul_apply`.  Stated for the concrete weight `f·Λ`, so the whole recursion chain
   needs only `f(mn) = f(m)f(n)` and `|f| ≤ 1` — no invertibility of `f 1`, and no Dirichlet inverse.
6. `sum_Icc_log_eq_log_factorial`, `abs_sum_Icc_mul_log_sub_le` — replacing the weight `log n` by
   `log N` costs `N log N − log N! ≤ N`, using the corpus's `le_log_factorial`.
7. `abs_sum_notPrimeVonMangoldt_weight_le` — **the prime-power excess is `O(N)`**: the corpus's Abel
   bound `RHTower.Mertens.tail_bounded` (`∑_{d ≤ N, d not prime} Λ(d)/d ≤ 8 + mertensTail`) applied
   termwise against the trivial divided size.
8. `abs_sum_Icc_mul_log_sub_sum_primes_le` — the signed prime-only identity.
9. `abs_sum_Icc_mul_log_sub_sum_primes_le'` — **the entry point**, the statement above.
10. `abs_sum_Icc_mul_log_le`, `abs_sum_Icc_mul_log_le_primes` — the absolute-value forms.

The only hypotheses anywhere in the chain are the two that define the function class,
`f(mn) = f(m)f(n)` and `|f(n)| ≤ 1`.  Nothing is assumed about the partial sums of `f`, at any scale:
statements of the form "if `S_f` is small below `N` then it is small at `N`" are excluded from this card,
because their premise is a fact about the object that cannot be discharged.

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

## The universal law behind it

The weight `Λ_f` is the logarithmic derivative of the Dirichlet ring, and this is now proved as such:

| Declaration | Statement |
|---|---|
| `pmul_log_mul` | `L(f*g) = L(f)*g + f*L(g)` for `L f = f·log` — the **Leibniz rule**: `log` is additive on the antidiagonal |
| `vonMangoldtOf_one` | `Λ_1 = 0` |
| `vonMangoldtOf_mul` | `Λ_{f*g} = Λ_f + Λ_g` — **the weight turns convolution into addition** |
| `vonMangoldtOf_zeta` | `Λ_ζ = Λ` |
| `pmul_moebius_log`, `vonMangoldtOf_moebius` | `μ·log = μ * (−Λ)`, i.e. `Λ_μ = −Λ` |
| `vonMangoldtOf_eq_pmul_vonMangoldt` | `Λ_f = f·Λ` for completely multiplicative `f` |

So `f ↦ Λ_f` is a homomorphism from the units of the Dirichlet ring to the additive group of arithmetic
functions, and the three classical weights are its values at the three classical units: `Λ` at `ζ`, `−Λ`
at `μ` (forced by `μ * ζ = 1` and additivity), and `f·Λ` at a completely multiplicative `f`.

The recursion is the *same* swap in every case. Its Möbius instance,
`sum_Icc_moebius_mul_log_eq`, is the classical identity

`∑_{n ≤ N} μ(n) log n = −∑_{d ≤ N} Λ(d)·M(⌊N/d⌋)`

and carries **no hypotheses at all**; the completely multiplicative instance carries only the two that
define the class, `f(mn) = f(m)f(n)` and `|f(n)| ≤ 1`.
