# Elliptic unipotent normalization preserves domain probability

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Left multiplication by any completed unipotent adele
  matrix, followed by canonical rational normalization, preserves the
  countable product of actual additive-domain Haar probabilities.

## Proof

Let `d` be a domain-valued free stream. For index `n`, let `d⁰` agree with
`d` below `n` and vanish from `n` onward. Triangular multiplication implies
that the streams of `g decode(d)` and `g decode(d⁰)` agree below `n`, and
their current coordinates differ by `dₙ`. The normalization increment law
therefore makes the normalized current coordinate equal to
`dₙ + φₙ(d_{<n})`, where `φₙ` is normalization of the zero extension.

The shift is continuous: zero extension, coefficient multiplication, and
normalization are continuous for their product topologies. The actual
additive domain has measurable joint addition and right-invariant Haar
probability. The proved countable triangular-translation theorem now gives
invariance of its product probability. This argument neither assumes an
ambient infinite-dimensional Haar measure nor interchanges infinite
integrals without the finite-marginal theorem.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentProbability.lean`:
`adeleUnipotentDomainAction_triangular`,
`measurePreserving_adeleUnipotentDomainAction`. Direct Lean check passed; both axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
