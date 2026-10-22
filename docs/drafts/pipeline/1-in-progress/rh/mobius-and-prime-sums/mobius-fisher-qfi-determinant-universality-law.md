# Möbius Fisher QFI–determinant universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- `tendsto_finiteMobiusDoubledErasedQFI`: finite doubled-clock erased QFI converges to
  `squarefreeMobiusCriticalProjectiveFisherEnergy`.
- `norm_infiniteMobiusCriticalFisherTangentLp_sq`: the completed infinite Fisher tangent has
  squared norm equal to that same projective-energy coordinate.
- `inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero` and
  `norm_infiniteMobiusSignedWeightLp_sq`: completed source and tangent are orthogonal and source
  has unit squared norm.
- `det_pointedFisherConnectionCompression_eq_neg_half_projectiveEnergy_sq`: every pointed-Fisher
  two-channel compression has determinant equal to negative one half the square of its projective
  Gram energy.
- `squarefreeMobiusCritical_pointedFisherConnectionCompression_exact_mixed_signature`: the
  arithmetic compression is Hermitian, nonsingular, and neither positive nor negative
  semidefinite.
- `tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy`: projective energy tends to `4` at the
  critical boundary.

Corpus research found no theorem identifying the finite doubled-clock QFI limit with the signed
determinant of the completed infinite pointed-Fisher connection.

## Universal law

At every `sigma > 1`, finite doubled-clock erased QFI reconstructs the completed infinite
pointed-Fisher compression determinant through the exact transform

`det M = -1/2 * (lim_N QFI_N)^2`.

Every interior compression is Hermitian, nonsingular, and mixed-signature. At the critical
boundary `sigma → 1+`, its determinant converges to `-8`.

## Paper proof

Unit source norm and source–tangent orthogonality reduce projective Gram energy to tangent norm
squared. The tangent norm theorem identifies this value with the arithmetic projective Fisher
energy. The generic pointed-connection determinant formula therefore gives the exact negative
half-square identity. Continuity of squaring transports the finite doubled-clock QFI limit through
that identity. The critical energy limit `4` gives determinant limit `-1/2 * 4^2 = -8`. The existing
independence theorem supplies the exact mixed-signature clause. No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.MobiusFisherQFIDeterminantUniversalityLaw`.

Exact command:
`lake env lean GaloisForLFunctions/RHTower/MobiusFisherQFIDeterminantUniversalityLaw.lean`.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
