# Degree-one discriminant tail stability — Lean certificate

- **ID:** `degree-one-discriminant-tail-stability-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `degree-one-discriminant-tail-stability.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`GaloisForLFunctions.HTGeometry.DegreeOneDiscriminantTailStability`
(umbrella: `GaloisForLFunctions.HTGeometry`).

## Exact certificates

- `degreeOneShiftedDet_tail_expansion` proves the exact five-term perturbation
  identity, and `abs_degreeOneShiftedDet_tail_expansion_le` proves its stated
  absolute error budget without replacing it by an operator-norm estimate.
- `degreeOneShiftedDet_pos_of_tail_margin` proves the strict determinant-margin
  criterion for the full degree-one shifted determinant.
- `degreeOneConjugatePair_det` proves the exact negative imaginary-defect
  square of one conjugate pair, while `degreeOneBulkConjugatePair_update`
  proves the exact finite-real-bulk update formula.

The result is an unconditional finite algebraic certificate over real moments
and complex conjugate-pair representatives. It does not introduce an RH,
zero-location, or numerical-tail premise.

## Verification

- Targeted leaf build:
  `lake build GaloisForLFunctions.HTGeometry.DegreeOneDiscriminantTailStability`.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
