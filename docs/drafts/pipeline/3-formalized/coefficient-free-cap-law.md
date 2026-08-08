# Coefficient-free bounds cannot beat the constant sequence

- **ID:** coefficient-free-cap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** If `B` majorises `Φ g` for every bounded completely multiplicative `g`, and
  `L ≤ Φ(1)`, then `L ≤ B`. If moreover the right-hand side is a function of the moduli alone, then
  `L ≤ B(‖f‖)` for every unimodular completely multiplicative `f`.

## Goal

Three architectures in this corpus turned out to be capped at the trivial size, and the arguments were
the same each time:

* `5-failed/modulus-first-vertical-integral-no-go.md` — the vertical integral of the modulus;
* `5-failed/ghs-prime-saving-master-bound-is-trivial.md` — any coefficient-free majorisation of the two
  GHS sieve mean squares;
* the same card's later section — the unconditional mean-square Cesàro chain, including the improved
  dyadic form.

In each case the bound's right-hand side does not mention the coefficient sequence — because it was
majorised through `‖a_n‖ ≤ A log n`, or because it is built from `‖a_n‖` alone — and the bound holds for
*every* bounded completely multiplicative sequence. Instantiating at the constant sequence `1`, whose
functional value is the trivial size, then bounds the right-hand side from below. Rediscovering that per
route is waste; worse, it invites reading each new estimate as progress.

## The law

`le_of_coefficientFree_bound` makes the test mechanical: to kill a route of this shape, exhibit

1. its bound as a `∀ g` statement whose right-hand side is sequence-free, and
2. a lower bound for the functional at the constant sequence.

Nothing about the analytic estimate enters, so no sharpening of it can evade the conclusion. That is the
substance: the caps are not quantitative accidents.

`le_of_modulusOnly_bound` is the sharper form. A right-hand side depending on the sequence only through
the moduli cannot separate *any* unimodular completely multiplicative sequence from the constant one —
which is the relevant comparison for the Liouville function, whose moduli are identically `1`. (For
Möbius the comparison is with `λ` rather than with `1`, since `‖μ(n)‖` vanishes off the squarefree
integers.)

`trivial_le_cesaro_dyadic_bound_of_law` recovers the Cesàro cap from the law, confirming that the
general test reproduces the hand-made instance.

## Lean

| Statement | Module |
|---|---|
| `le_of_coefficientFree_bound` | `RHTower/Sieve/CoefficientFreeCap.lean` |
| `le_of_modulusOnly_bound` | `RHTower/Sieve/CoefficientFreeCap.lean` |
| `trivial_le_cesaro_dyadic_bound_of_law` | `RHTower/Sieve/CoefficientFreeCap.lean` |

Unconditional: `[propext, Classical.choice, Quot.sound]`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3
- [ ] 3 → 4

## Log
- 2026-08-09 — created in 3-formalized; the mechanism behind three separate no-gos stated once.

## Running the test: what escapes, and what stops it instead

Applying the law to the folder's remaining partial-sum capstones turned up a scope limit worth stating.
`CesaroPartialSumBound.norm_sum_Icc_le_cesaro_damped` has a sequence-free right-hand side, but it is
parametrised by a distance level `δ` whose admissibility is a hypothesis *about the sequence*
(`δ ≤ 𝔻(f, n^{it})` uniformly). At the constant sequence that hypothesis forces `δ = 0` — the distance
from `1` to the trivial character vanishes — so instantiation yields the undamped bound and no cap. The
damped chains therefore escape `le_of_coefficientFree_bound`, and any future route that carries a genuine
distance input escapes it too. That is the correct reading of the law: it convicts coefficient-blind
majorisation, not arithmetic input.

What stops the damped chain is quantitative, and unconditional. The distance to a character is at most
twice the prime mass, since `1 − Re(f(p)conj(g(p))) ≤ 2` for bounded `f`, `g`
(`DampedSizeFloor.mulDistSqPair_le_two_mul_sum_inv`), so any legitimately available `δ` satisfies
`δ² ≤ 2∑_{p ∈ P}1/p` and

`dampedSize σ δ z L ≥ (1 + 1/(σ−1))exp(7/2 + 2(σ−1)(log z + log 4) − 2∑_{p ≤ z}1/p)`

(`dampedSize_ge_of_dist`, via the monotone form `dampedSize_ge_of_sq_le`). With
`∑_{p ≤ z}1/p = logLog z + O(1)` the exponential is `≍ (log z)^{-2}`; writing `A = (σ−1)log L` and `z = L`,
the two parts of `dampedSize` are `≳ (e^{2A}/A)(log L)^{-1}` and `(log L/A)e^{-A}`, minimised together at
`A ≍ (2/3)logLog L` where both are `≍ (log L)^{1/3}/A`. So

`dampedSize ≳ (log L)^{1/3}/logLog L`

for every admissible `σ` and `δ`, whatever zero-free region supplies the distance. The damped analytic
term is never `o(1)`, so that chain cannot reach `o(N)` either — and the reason is now separated from the
coefficient-free cap: the damping available is bounded by the total prime mass, while the truncation tail
forces the abscissa up and `e^{2(σ−1)log z}` charges it back.

## The uniform distance, and why the borderline is a theorem

The floor above used `δ² ≤ 2∑_p 1/p`, which is attained at a *single* frequency — for `f(p) = −1` at
`t = 0`. A damped route needs a level uniform over a whole range, and averaging over the range halves it.
Expanding `Re(f(p)·conj(charFn t p)) = Re(f(p))cos(t log p) + Im(f(p))sin(t log p)`
(`UniformDistanceAverage.re_mul_conj_charFn`) and integrating the two elementary antiderivatives,

`|∫_0^T Re(f(p)·conj(charFn t p)) dt| ≤ 3/log p`

(`abs_integral_re_mul_conj_charFn_le`, unconditional for every `p ≥ 2` and every bounded `f`). Summing
against `1/p`, the average of the distance over `[0,T]` is at most
`∑_{p ∈ P}1/p + (3/T)∑_{p ∈ P}1/(p log p)`, so some frequency in the range attains that: the uniform level
is the prime mass, not twice it.

That is what makes the Euler bound's borderline a theorem rather than a limitation of the estimate. With
`e^{−δ²} ≳ e^{−∑_p 1/p} ≍ (log z)^{-1}`, the first part of `dampedSize` is `≳ (log z/A)e^{2A}(log z)^{-1}`,
whose minimum over `A = (σ−1)log z` is `Θ(1)`. So even with the truncation tail removed — the one part that
was fixable — the damped analytic term is `Θ(x^σ)`, exactly the trivial size. The pointwise Euler route
sits on the borderline by construction, and no choice of abscissa moves it off.

What remains open is the tail sum `∑_p 1/(p log p) = O(1)`, needed to make the error term above absolute
rather than `O(logLog z/T)`; by Mertens per dyadic block it is `≍ ∑_k 1/k²`, so it is a bounded quantity,
but the corpus does not yet carry it.

### First piece of the missing tail sum

The two-sided Mertens first theorem is in the corpus (`MertensFirst.mertensFirst_upper`,
`mertensFirst_lower`), so differencing it at consecutive powers of two bounds a dyadic block of primes by
an absolute constant:

`∑_{2^k < p ≤ 2^{k+1}} (log p)/p ≤ log 2 + log 4 + 1 + 2·logSqTailConst`

(`MertensFirstBlock.sum_prime_log_div_block_le`), uniformly in `k` — the upper bound at `2^{k+1}`
contributes `(k+1)log 2 + log 4`, the lower bound at `2^k` removes `k log 2 − 1 − 2·logSqTailConst`, and
the `k log 2` cancels.

That is the per-block input the tail sum needs, and the assembly is now done. Grouping the primes by
`k = Nat.log 2 p` — a fibrewise decomposition, not a `biUnion`, so it is an identity rather than an
inequality (`Finset.sum_fiberwise_of_maps_to`) — the fibre at `k` has `2^k ≤ p < 2^{k+1}`, hence
`log p ≥ k log 2` and `1/(p log p) ≤ ((log p)/p)/(k log 2)²`. For `k ≥ 2` the fibre sits inside the dyadic
block `(2^k, 2^{k+1}]`, because the endpoint `2^k` is not prime; for `k = 1` it sits inside `primesLE 4`,
whose mass is at most `2 log 4`. Summing `1/k²` over `k ≤ Nat.log 2 x` with the corpus's
`sum_inv_sq_le_two`:

`∑_{p ≤ x} 1/(p log p) ≤ 2·max(mertensBlockConst, 2 log 4)/(log 2)²`

(`PrimeInvLogTail.sum_prime_inv_mul_log_le`), uniformly in `x`.

### The averaging theorem

With the tail sum in hand the argument closes:

`∫_0^T 𝔻(f, n^{it})² dt ≤ T·∑_{p ≤ x}1/p + 3·primeInvLogConst`
(`UniformDistanceAverage.integral_mulDistSqPair_le`), hence

`∃ t ∈ [0,T],  𝔻(f, n^{it})² ≤ ∑_{p ≤ x}1/p + 4·primeInvLogConst/T`

(`exists_mulDistSqPair_le_prime_mass`), for every bounded `f` and every `T > 0`. The slack `4` rather
than `3` avoids needing strict integral monotonicity: assuming the negation gives
`T·A + 4C ≤ T·A + 3C`, so `C ≤ 0`, contradicting `primeInvLogConst_pos`.

So the uniform distance level available to a damped route is the prime mass up to `O(1/T)`, with no
`z`-dependence at all — never the `2∑_p 1/p` that a single frequency can attain. That is the sharp input
to the `dampedSize` floor: `e^{−δ²} ≳ e^{−∑_p 1/p} ≍ (log z)^{-1}` uniformly, so the floor is `Θ(1)` and
the Euler borderline is unconditional.
