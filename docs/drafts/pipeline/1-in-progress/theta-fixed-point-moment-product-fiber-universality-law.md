# Theta fixed-point moment/product-fibre universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `thetaCuspTailSecondDensityAtomPhase_eq_arithmeticEndpoint_sub_sq_potential`: each atom value is
  an affine endpoint jet minus a `z²` potential remainder.
- `thetaCuspTailSecondDensityAtomPhaseDerivative_eq_arithmeticEndpoint_sub_sq_potential`: the
  derivative has the companion endpoint/potential normal form.
- `thetaCuspTailSecondDensityAtomPhase_zero`: at `z=0`, the atom value is its zeroth moment.
- `thetaCuspTailSecondDensityAtomPhaseDerivative_zero`: at `z=0`, its derivative is `i` times its
  first moment.
- `thetaProductFiberActualPhaseCurrent_zero`: every fixed-point product-fibre current is a finite
  sum of products of those moments.

The normal-form and completed-valuation theorems describe literally the same atom evaluations.
Corpus research found no theorem eliminating the potentials at the reflection fixed point and
closing the resulting moment/product-fibre formulas.

## Universal law

For every positive square index, the zeroth density moment equals
`(8πn²-2) exp(-πn²)` and the first equals `4 exp(-πn²)`. Consequently every product-fibre current
at `z=0` is an explicit finite Gibbs sum of products of those endpoint weights.

## Paper proof

Set `z=0` in both arithmetic potential normal forms. Every potential term vanishes because it is
multiplied by `z` or `z²`. Compare real parts with the fixed-point value/moment identity and
imaginary parts with the derivative/moment identity. Substitute both formulas into the existing
product-fibre current formula. No numerical computation is used.

## Lean formalization

Module: `GaloisForLFunctions.RHTower.ThetaFixedPointMomentProductFiberUniversalityLaw`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
