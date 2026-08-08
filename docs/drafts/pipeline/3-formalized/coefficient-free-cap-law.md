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
