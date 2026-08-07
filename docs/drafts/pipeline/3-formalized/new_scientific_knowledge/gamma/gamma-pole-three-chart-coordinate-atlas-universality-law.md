# Gamma pole three-chart coordinate-atlas universality law

## Status

Stage 3-formalized: fully proven on paper and formalized unconditionally in Lean 4.

## Theorem-first source

- `gammaPole_finitePart_covariantResidue_coordinateFieldUniversality`: finite-part jets and
  covariant residues are mutually invertible polynomial frames over `ℂ(N)` after adjoining the
  reciprocal factorial scale.
- `universalUnitInverseCoefficientRationalMap_involutive`: formal unit inversion is involutive.
- `universalTangentInverseCoefficientMap_involutive`: tangent-to-identity compositional inversion
  is involutive.
- `gammaPoleScaleAndInverseBranchCoefficientEval_eq_comp`: normalized nonlinear inverse-branch
  coefficients are obtained by tangent compositional inversion of reciprocal-unit coefficients.
- `gammaPoleScaleAndInverseBranchCoefficientEval_injective`: the complex-base inverse-branch
  evaluation is faithful.

The inverse-branch theorem existed only over `ℂ`, and the corpus never compared its coordinate
algebra with either moving-center finite-part or covariant-residue frames.

## Universal law

Over the full rational moving-pole field `ℂ(N)`, the reciprocal factorial scale together with
finite-part jets, covariant simple-zero residues, or normalized nonlinear inverse-Gamma branch
coefficients gives three pairwise polynomial coordinate systems for exactly the same evaluated
algebra.  Explicit changes of coordinates are mutual inverses, preserve evaluation, and make the
representative of every polynomial observable unique in each other chart.

## Paper proof

Extend tangent compositional inversion from `ℂ` to `ℂ(N)` by base change; its involution identity
and injectivity survive.  Lift it while fixing the scale coordinate.  If `A` denotes the nonzero
diagonal finite-part scaling, `I` formal unit inversion, and `T` tangent compositional inversion,
then inverse-branch evaluation factors as `U I T`, whereas finite-part evaluation is `U A`.
Therefore `A⁻¹ I T` and `T I A` are mutual inverse coordinate rewrites.  Evaluation conjugacy and
faithfulness give unique representatives.  Compose these rewrites with the already-proved
finite-part/covariant-residue rewrites to obtain both residue/inverse-branch directions and hence
the complete three-chart atlas.

## Lean formalization

- Module:
  `GaloisForLFunctions.HTGeometry.GammaPoleScalePrincipalRemainderUniversalityLaw`
- Rational inverse-branch evaluation:
  `GaloisForLFunctions.gammaPoleScaleAndInverseBranchCoefficientRationalEval`
- Finite-part/inverse-branch theorem:
  `GaloisForLFunctions.gammaPole_finitePart_inverseBranch_coordinateFieldUniversality`
- Three-chart theorem:
  `GaloisForLFunctions.gammaPole_finitePart_covariantResidue_inverseBranch_coordinateAtlasUniversality`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/GammaPoleScalePrincipalRemainderUniversalityLaw.lean`
  passed on 2026-07-22.

## Verification gate (passed)

The duplicate-declaration blocker recorded earlier is gone: `GammaFactorialSecondJetHarmonicResidue.lean`
owns `shiftedHarmonicPowerSum`, `iteratedDeriv_digamma_neg_nat_add_of_ne_int` and
`gammaFactorialScaledPolygamma`, `GammaFactorialAllOrderPoleJet.lean` keeps only the derived
statements, and the whole import cone elaborates.  Every theorem named above resolves and
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.

## Stage-3 Lean certificate

```text
gammaPole_finitePart_covariantResidue_inverseBranch_coordinateAtlasUniversality
gammaPole_finitePart_inverseBranch_coordinateFieldUniversality
gammaPoleScaleAndInverseBranchCoefficientEval_injective
universalTangentInverseCoefficientMap_involutive
universalUnitInverseCoefficientRationalMap_involutive
```

Every declaration named above was resolved against the built Lean tree and `#print axioms`
reported only `propext`, `Classical.choice`, `Quot.sound`.  `scripts/formal_tools.py lint`
reports no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the tree.
