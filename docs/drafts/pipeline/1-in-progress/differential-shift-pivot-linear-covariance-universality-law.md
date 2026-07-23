# Differential shifted-pivot linear covariance universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/DifferentialLinearChangeAutomorphism.lean`
  - `differentialJetLinearChangeAlgEquiv`
  - `differentialJetLinearChangeAlgHom_derivation`
- `HTGeometry/DifferentialIndependentLinearForms.lean`
  - `differentialJet_matrixLinearForms`
- `HTGeometry/DifferentialShiftPivotRelationIdeal.lean`
  - `differentialRelationIdeal_sumElim_eq_shiftPivot`
- `HTGeometry/DifferentialPolynomial.lean`
  - `differentialPolynomialEval`
  - `differentialRelationIdeal`

## Universal law

For every invertible constant matrix, evaluation after its jetwise differential-polynomial
automorphism is identical to evaluation on the linearly recombined source family.  Hence a
differential polynomial is a relation of the recombined family exactly when its automorphic image
is a relation of the original family.

Applied to every differentially independent shifted-pivot system, this says its complete displayed
relation ideal remains complete after arbitrary invertible mixing of all pivot and dependent
coordinates.  The transformed family need not retain a visible single-pivot presentation: its full
ideal is still the inverse image of the original explicit shifted-pivot ideal.

## Paper proof

Check the evaluation identity on every formal jet generator.  Constant coefficients have zero
derivative, so the jet of a matrix linear form is the same matrix linear form in the corresponding
jets.  Algebra-homomorphism extensionality gives the identity for every differential polynomial.
Kernel membership then gives contravariant covariance of relation ideals.  Substitute the complete
shifted-pivot kernel theorem for the original relation ideal.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/DifferentialShiftPivotLinearCovarianceUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/HTGeometry/DifferentialShiftPivotLinearCovarianceUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
jetwise linear differential automorphisms and complete shifted-pivot relation ideals separately,
but no evaluation covariance or transformed-ideal theorem joining them.
