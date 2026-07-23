# Gamma finite-part/covariant-residue coordinate-field universality law

## Status

Fully proven on paper; formalized in Lean 4.

## Theorem-first source

- `gammaPoleScaleAndFinitePartJetRationalEval_eq_comp`: finite-part jets are a nonzero diagonal
  transform of regular-unit coefficients after adjoining the reciprocal factorial scale.
- `gammaPoleScaleAndCovariantResidueRationalEval_eq_comp`: covariant residues are a nonzero
  diagonal transform of reciprocal-unit coefficients in the same scale frame.
- `universalUnitInverseCoefficientRationalMap_involutive`: formal inversion of a unit power series
  is an involution over the rational moving-center field.
- `gammaPoleScaleAndFinitePartJetRationalEval_injective` and
  `gammaPoleScaleAndCovariantResidueRationalEval_injective`: both coordinate evaluations are
  faithful.

The corpus proved freeness of the two frames separately, but no theorem identified their
evaluated polynomial algebras or supplied translations between them.

## Universal law

After adjoining the reciprocal signed-factorial pole scale over `ℂ(N)`, analytic Gamma finite-part
jets and covariant simple-zero residues are two polynomial coordinate systems for exactly the same
evaluated algebra.  Explicit coordinate rewrites in both directions are mutual inverses, preserve
evaluation, and give every polynomial observable in either frame a unique representative in the
other.

## Paper proof

Let `A` diagonally rescale regular-unit coordinates to finite-part jets, let `R` diagonally rescale
reciprocal-unit coordinates to covariant residues, and let `I` be formal unit inversion lifted
while fixing the distinguished scale coordinate.  The two changes of coordinates are
`A⁻¹ I R` and `R⁻¹ I A`.  Nonzero diagonal entries make `A` and `R` invertible, while formal unit
inversion gives `I² = 1`.  Therefore the displayed changes are mutual inverses.  Existing
factorizations of the two evaluation maps show that each change preserves every evaluated
polynomial.  Injectivity of both evaluations makes each translated representative unique.

## Lean formalization

- Module:
  `GaloisForLFunctions.HTGeometry.GammaPoleScalePrincipalRemainderUniversalityLaw`
- Coordinate maps:
  `GaloisForLFunctions.gammaPoleCovariantResidueToFinitePartRationalMap` and
  `GaloisForLFunctions.gammaPoleFinitePartToCovariantResidueRationalMap`
- Evaluation conjugacies:
  `GaloisForLFunctions.gammaPoleScaleAndFinitePartJetRationalEval_comp_residueToFinitePart` and
  `GaloisForLFunctions.gammaPoleScaleAndCovariantResidueRationalEval_comp_finitePartToResidue`
- Universal theorem:
  `GaloisForLFunctions.gammaPole_finitePart_covariantResidue_coordinateFieldUniversality`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/GammaPoleScalePrincipalRemainderUniversalityLaw.lean`
  passed on 2026-07-22.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.
