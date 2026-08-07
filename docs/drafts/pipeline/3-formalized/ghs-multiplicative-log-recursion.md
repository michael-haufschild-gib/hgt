# The prime-only form of Halász's recursion, and the weight as a logarithm

- **ID:** ghs-multiplicative-log-recursion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every completely multiplicative `f : ℕ → ℂ` with `‖f‖ ≤ 1`,

  `‖S_f(N)·log N − ∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋)‖ ≤ (9 + mertensTail)·N`,
  where `S_f(M) = ∑_{m ≤ M} f(m)`.

  Hypotheses: complete multiplicativity and `‖f‖ ≤ 1`. Nothing else — in particular nothing is assumed
  about the partial sums of `f` at any scale.

## Why this route

The contour route to Halász's theorem is closed by three no-gos recorded on
`halasz-programme-session-index.md`: the pointwise damped bound loses `(log N)²`, and the mean-square
repair is worse than pointwise in the regime of the application (`L ≍ x`, `T` polylog). The third no-go
named the alternative: Halász's own proof uses the *multiplicative factorisation* of `f`, never forming a
Dirichlet polynomial of length `x`. That is this card.

## What the corpus already had

The audit found four of the needed pieces already proved, three of them for other purposes:

| Existing declaration | Content |
|---|---|
| `RHTower.Sieve.sum_divisors_swap` | the divisor swap `∑_{m ≤ N} ∑_{d ∣ m} G(d, m/d) = ∑_{d ≤ N} ∑_{k ≤ N/d} G(d,k)` |
| `RHTower.Sieve.sum_mul_log_eq_vonMangoldt` | **Halász's recursion** `∑_{m ≤ N} f(m) log m = ∑_{d ≤ N} Λ(d) f(d) S_f(⌊N/d⌋)` for completely multiplicative `f : ℕ → ℂ` |
| `RHTower.pmul_log_mul` | the Leibniz rule: pointwise `log` is a derivation of the Dirichlet ring (real coefficients; `HTGeometry.logWeight_leibniz` is the complex form) |
| `RHTower.Sieve.moebius_pmul_log`, `sum_moebius_mul_log_eq` | `μ·log = −(Λ * μ)` and its summed form |
| `RHTower.Mertens.tail_bounded` | `∑_{d ≤ N, d not prime} Λ(d)/d ≤ 8 + mertensTail`, by Abel summation against Chebyshev's `ψ − θ` |
| `RHTower.Sieve.le_log_factorial` | `N log N − N ≤ log N!` |

Nothing above was rebuilt. The recursion is consumed as it stands, over `ℂ`.

## What was missing, and is now proved

`RHTower/Sieve/MultiplicativeLogRecursion.lean` — the passage from the recursion to the primes:

1. `sum_Icc_log_eq_log_factorial` — `∑_{n ≤ N} log n = log N!`.
2. `norm_sum_Icc_mul_log_sub_le` — **the log-shift**: replacing the weight `log m` by the constant
   `log N` costs `∑_{m ≤ N}(log N − log m) = N log N − log N! ≤ N`.
3. `norm_sum_Icc_le` — the trivial size `‖S_f(M)‖ ≤ M`.
4. `norm_sum_notPrimeVonMangoldt_weight_le` — **the prime-power excess is `O(N)`** against any weight of
   the trivial divided size; this is where `tail_bounded` is consumed.
5. `norm_sum_Icc_mul_log_sub_sum_primes_le` — the signed prime-only identity for `∑ f(m) log m`.
6. `norm_sum_Icc_mul_log_sub_sum_primes_le'` — **the entry point**, the statement at the top of this card.

`RHTower/Sieve/VonMangoldtWeightAdditive.lean` and `HTGeometry/GeneralisedVonMangoldt.lean` — the weight
itself as a universal object:

| Declaration | Statement |
|---|---|
| `vonMangoldtOf f hf` | `Λ_f := f⁻¹ * (f·log)`, for `f 1` invertible |
| `pmul_log_eq_mul_vonMangoldtOf` | `f·log = f * Λ_f` — the defining identity |
| `eq_vonMangoldtOf_of_mul_eq` | uniqueness of the solution |
| `vonMangoldtOf_zeta` | `Λ_ζ = Λ` |
| `vonMangoldtOf_eq_pmul_vonMangoldt` | `Λ_f = f·Λ` for completely multiplicative `f` |
| `abs_vonMangoldtOf_le_vonMangoldt` | `\|Λ_f\| ≤ Λ` for `\|f\| ≤ 1` |
| `vonMangoldtOf_one` | `Λ_1 = 0` |
| `vonMangoldtOf_mul` | **`Λ_{f*g} = Λ_f + Λ_g`** — from the existing Leibniz rule |
| `vonMangoldtOf_moebius` | `Λ_μ = −Λ` — from the existing Möbius log identity |

So `f ↦ Λ_f` is a homomorphism from the units of the Dirichlet ring to the additive group of arithmetic
functions, and the three classical weights are its values at the three classical units: `Λ` at `ζ`, `−Λ`
at `μ` (forced by `μ * ζ = 1` and additivity), `f·Λ` at a completely multiplicative `f`. The three
recursions in the corpus — Halász's, the Möbius one, and the `∑_{m ≤ n} log m = ∑_{d ≤ n} Λ(d)⌊n/d⌋`
count — are the same swap applied to three values of one weight.

## What it does and does not give

It does **not** give decay, and no decay is claimed. The identity is exact up to `O(N)` and is satisfied
by `f = 1`, where both sides are `≍ N log N`. Its content is a strict reduction:

* the only values of `f` that matter are the values at **primes**, with weight `log p`;
* they enter **signed**, so all cancellation is preserved;
* the partial sums that appear are at the **divided scales** `⌊N/p⌋` only — no Dirichlet polynomial of
  length `N`, no mean-value theorem at a short height, hence none of the regime obstruction that closed
  the contour route.

Decay of `S_f` is now exactly equivalent to cancellation in `∑_{p ≤ N} f(p) log p · S_f(⌊N/p⌋)`, which is
where a distance hypothesis on the values `f(p)` acts. That is the next gate.

Two statements were deliberately **not** kept: the absolute-value forms of the recursion (they discard the
cancellation and provably cannot decay — `f = 1` saturates them), and any statement of the shape "if
`S_f` is small at all scales below `N` then it is small at `N`", whose premise is a fact about the object
that cannot be discharged.

## Relation to the RH programme

Route E's dependency chain terminates at `MRBilinear`, i.e. at Matomäki–Radziwiłł, which needs Halász's
theorem as an input. This card reopens the road to Halász after the contour route was closed, so it is
upstream of the Route E wall, not a new claim about RH.
