# Compact logarithmic torsion without Hilbert–Schmidt summability

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Logarithmic completion](riac-logarithmic-torsion-completion.md)

## Statement

For every `α>2`, the original logarithmic torsion operator is compact and
self-adjoint, but not Hilbert–Schmidt. Its normalized diagonal square sum
diverges for every real logarithmic exponent `α`.

## Proof

Put `L(n)=1+log n`. Inclusion from logarithmic exponent `α` to `β<α`
multiplies normalized coordinates by `L(n)^((β−α)/2)`. This multiplier
is bounded by one and tends to zero, so the inclusion is compact. Its
arithmetic coefficients are exactly preserved.

Choose `2<β<α`. The original absolutely convergent torsion pair series
factors through this inclusion on both arguments. Composition with bounded
maps preserves compactness, including passage to the Riesz representative.
Self-adjointness follows from symmetry of the same pair series.

The normalized diagonal is `d(n)/L(n)^α`. On even prime conductors,
`d(2p)≥log 2`. Choose a natural integer `N>2α`. Eventually
`L(2p)≤(2+log 2)log p`, giving

`d(2p)²/L(2p)^(2α) ≥ (log 2)²/((2+log 2)^N(log p)^N)`.

The formalized prime-log divergence theorem makes the right-hand series
diverge, using Euler's prime reciprocal divergence. The map `p↦2p−1`
is injective in the normalized conductor coordinates, so the full diagonal
square sum diverges. Hilbert–Schmidt membership would make the squared
operator-image norms summable; Cauchy–Schwarz bounds each diagonal square
by its corresponding squared image norm, a contradiction.

## Scope and positive survivor

These statements concern the original torsion operator on the logarithmic
carrier. They do not assert compactness after adding a constant identity
correction. The positive survivor is its exact compact self-adjoint
realization with the original arithmetic series retained. No signed
local-index bound or arithmetic height positivity follows.

The [power–logarithmic refinement](../0-backlog/riac-power-logarithmic-spectral-boundary.md)
at conductor exponent `δ=1/2` remains a separate conjecture.

## Lean statements

- [LogarithmicTorsionCompactness](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/LogarithmicTorsionCompactness.lean):
  `logarithmicProbeInclusion_coefficients`, `logarithmicProbeInclusion_compact`,
  `logarithmicTorsionForm_factor`, `logarithmicTorsionOperator_compact`.
- [LogarithmicTorsionNotHilbertSchmidt](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/LogarithmicTorsionNotHilbertSchmidt.lean):
  `logarithmicTorsionDiagonal_not_summable`,
  `logarithmicTorsionOperator_not_hilbertSchmidt`.

Both direct checks pass. All nine printed axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
