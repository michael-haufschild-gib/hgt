# Gamma pole scale/principal-remainder universality law

## Status

Fully proven on paper; formalized in Lean 4.

## Theorem-first source

- `gammaPoleFinitePartJetGerm_eq_unitCoefficient`: finite-part jet `m` is the exact nonzero
  rescaling `-m!` of regular-unit coefficient `m`.
- `algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficient_over_ratFunc`: reciprocal
  factorial scale and all positive regular-unit coefficients are jointly algebraically independent
  over `ℂ(N)`.
- `mvPolynomialDiagonalScaleRing_injective`: a coordinatewise nonzero rescaling preserves the
  polynomial coordinate algebra.

The corpus separately had finite-part freeness and scale--unit freeness, but no scale--finite-part
closure.

## Universal law

Across the complete normalized Gamma pole tower, the reciprocal signed-factorial scale together
with every jet of the canonical analytic remainder after principal-part subtraction is jointly
algebraically independent over the full rational moving-pole field `ℂ(N)`.  This remains faithful
after Laurent localization at the factorial scale: no finite relation using positive or negative
scale powers and polynomial finite-part-jet coefficients can vanish on the pole tower.

## Paper proof

Index the scale by `none` and finite-part jet `m` by `some m`.  The exact value-reflection theorem
identifies this family with the already-free scale--unit family after multiplying coordinate
`some m` by `-m!` and leaving `none` unchanged.  Every diagonal multiplier is nonzero.  Hence the
diagonal polynomial endomorphism is injective.  Composing it with the injective scale--unit
evaluation yields injective evaluation on the scale--finite-part family, equivalent to algebraic
independence over `ℂ(N)`.  Separating the scale through the polynomial/`Option` coordinate
equivalence gives injective polynomial evaluation; localization at the scale stays injective
because the evaluated scale is a unit.

## Lean formalization

- Module:
  `GaloisForLFunctions.HTGeometry.GammaPoleScalePrincipalRemainderUniversalityLaw`
- Theorem:
  `GaloisForLFunctions.algebraicIndependent_gammaPoleScaleAndFinitePartJet_over_ratFunc`
- Laurent theorem:
  `GaloisForLFunctions.gammaPoleScaleAndFinitePartJetLaurentEval_injective`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/GammaPoleScalePrincipalRemainderUniversalityLaw.lean`
  passed on 2026-07-22.

## Verification gate (blocked)

`lake build GaloisForLFunctions.HTGeometry.GammaPoleScalePrincipalRemainderUniversalityLaw` currently
fails **inside a dependency**, not in this module: `GammaFactorialAllOrderPoleJet.lean` and
`GammaFactorialSecondJetHarmonicResidue.lean` both declare `GaloisForLFunctions.shiftedHarmonicPowerSum`,
`GaloisForLFunctions.iteratedDeriv_digamma_neg_nat_add_of_ne_int` and
`GaloisForLFunctions.gammaFactorialScaledPolygamma`, so the older module no longer elaborates once
both are in one import cone.  The named theorems of this card are unaffected in content; promotion
waits on the duplicate-name resolution in the `GammaFactorial*` cone.

## Novelty audit

Pending literature audit after theorem-generation phase.  Corpus audit is negative.
