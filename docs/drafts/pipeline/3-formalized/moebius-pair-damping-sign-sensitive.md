# The Möbius smooth sums at `t` and `2t` cannot both be large

- **ID:** moebius-pair-damping
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `f` bounded multiplicative with `f(p) = −1` on a finite set `P` of primes,
  `‖S(t)‖·‖S(2t)‖ ≤ exp(2∑_{p∈P}1/p + 2∑_{p∈P}1/p² − (2/5)∑_{p∈P}1/p)`, where `S` is the smooth
  multiplicative sum. Equivalently `min(‖S(t)‖,‖S(2t)‖) ≤ exp(∑1/p + ∑1/p² − (2/5)∑1/p)`.

## Goal

Two architectural no-gos proved in this corpus say the same thing from different heights:
`modulus-first-vertical-integral-no-go.md` — passing to the integral of the modulus caps a Perron route
at the trivial size; `ghs-prime-saving-master-bound-is-trivial.md` — majorising the sieve mean squares
by anything coefficient-free caps the GHS route at the trivial size. In both cases the step that kills
the route discards a *sign*: of the integrand's phase in the first, of the coefficients in the second,
and `|μ(n)| = |1(n)|` on the squarefree integers. So a route can only work if some step is
sign-sensitive.

The corpus contains exactly one sign-sensitive damping tool, and it had no consumer:
`MoebiusDistance.three_add_four_cos_add_cos_two`, the identity `3 + 4cos θ + cos 2θ = 2(1 + cos θ)²`,
whose consequence `two_mul_sum_inv_div_five_le_max` reads
`(2/5)∑_{p∈P}1/p ≤ max(𝔻(f,n^{it})², 𝔻(f,n^{2it})²)` when `f(p) = −1`. This card supplies the consumer.

## The mechanism

The maximum is attained at `t` or at `2t`. Feed it into the damped Euler bound
(`HalaszDichotomy.norm_sum_smooth_le_exp_of_far`) at whichever frequency attains it, and the trivial
Euler bound at the other. The product of the two smooth sums then loses `(2/5)∑_p 1/p` in the exponent.
With `∑_{p ≤ z}1/p = logLog z + O(1)` the trivial product bound is `≍ (log z)²` and this is
`≍ (log z)^{8/5}`.

No zero-free region, no distance hypothesis, no sieve level: only `μ(p) = −1`. The saving is small, but
it is of a kind the two no-gos prove no amount of majorisation can produce — it is the sign of the
coefficients doing the work.

## Lean

| Statement | Module |
|---|---|
| `norm_smoothMulSum_mul_norm_smoothMulSum_two_le` | `RHTower/Sieve/MoebiusPairDamping.lean` |
| `min_norm_smoothMulSum_le` | `RHTower/Sieve/MoebiusPairDamping.lean` |

Unconditional: `[propext, Classical.choice, Quot.sound]`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3
- [ ] 3 → 4

## Log
- 2026-08-08 — created in 3-formalized; the sign-sensitive identity given its first consumer.

## The ratio tends to 1

The `2/5` is the case `K = 2` of a family. With `θ_p = t·log p`, the positivity of the
pair-correlation form — `0 ≤ ∑_{j,k < K+1} cos((j−k)θ)`, which is `|∑_{j<K+1}e^{ijθ}|² ≥ 0`, the Fejér
kernel, and is already in the corpus as `RHTower.pair_correlation_nonneg` — gives

`∑_{j,k < K+1} 𝔻(f, n^{i(j−k)t})² ≥ (K+1)²·A`,   `A = ∑_{p ∈ P}1/p`,

while the `K+1` diagonal terms contribute exactly `2(K+1)A`. Averaging over the `(K+1)K` off-diagonal
pairs and using that the distance is even in the frequency,

`∃ k ∈ [1,K],  𝔻(f, n^{ikt})² ≥ ((K−1)/K)·A`

(`exists_mulDistSqPair_ge_of_neg_one`). At `K = 2` this is the `2/5`; the ratio tends to `A` itself.
Feeding it into the damped Euler bound:

`∃ k ∈ [1,K],  ‖S(kt)‖ ≤ exp(A/K + B)`

(`exists_norm_smoothMulSum_le_of_neg_one`), against the trivial `exp(A + B)`. At `P = {p ≤ z}` the
saving is `(log z)^{-(1-1/K)}`, so for every `ε > 0` some frequency among `t, 2t, …, Kt` has a smooth sum
of size `(log z)^{ε}` — unconditional, no zero-free region, no distance hypothesis. Only the sign
`f(p) = −1` is used, which is exactly what the two architectural no-gos say a route must use.

| Statement | Module |
|---|---|
| `mulDistSqPair_neg_one_charFn_neg` | `RHTower/Sieve/MoebiusFejerDistance.lean` |
| `sq_le_sum_sum_mulDistSqPair` | `RHTower/Sieve/MoebiusFejerDistance.lean` |
| `exists_mulDistSqPair_ge_of_neg_one` | `RHTower/Sieve/MoebiusFejerDistance.lean` |
| `exists_norm_smoothMulSum_le_of_neg_one` | `RHTower/Sieve/MoebiusFejerDistance.lean` |
