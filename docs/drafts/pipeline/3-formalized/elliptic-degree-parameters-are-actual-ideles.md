# Elliptic degree parameters are actual ideles

- **Stage:** 3-formalized
- **Parent:** [Arithmetic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Actual elliptic ideles `η_d`, for every natural `d`, satisfy
  `|η_d|=3^d`, `log|η_d|=d log 3`, and
  `χ_s(η_d)=exp(s d log 3)`.

## Proof

The audited infinity simple pole with coefficient one has valuation
`exp(1)`, hence is nonzero. Combine this local unit with units one at every
finite place. Both the element and its inverse are restricted, giving an
actual idele. Its finite magnitudes are one; the residue-three infinity
normalization gives magnitude three. Its `d`th power has magnitude `3^d`
by multiplicativity. Taking the real logarithm and substituting the actual
spectral-character definition prove the remaining identities.

No invariance of the arithmetic subgroup under this rotation is asserted.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticDegreeIdeles.lean`:
`ideleMagnitude_degree`, `log_ideleMagnitude_degree`, `ideleCharacter_degree`.
Direct Lean and transitive axiom audits passed; dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
