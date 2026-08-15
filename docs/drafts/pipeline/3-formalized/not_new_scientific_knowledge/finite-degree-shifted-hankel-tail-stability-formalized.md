# Finite-Degree Shifted Hankel Tail Stability — Lean certificate

- **ID:** `finite-degree-shifted-hankel-tail-stability-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `finite-degree-shifted-hankel-tail-stability.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`GaloisForLFunctions.HTGeometry.FiniteDegreeShiftedHankelTailStability`
(umbrella: `GaloisForLFunctions.HTGeometry`).

## Exact certificates

- `finiteDegreeShiftedHankelLambdaMin` is the literal infimum of the Rayleigh
  quotient on nonzero real vectors.  The theorem
  `finiteDegreeShiftedHankel_lambdaMin_mul_dotProduct_le` turns that exact
  value into the stated bulk quadratic lower bound.
- `abs_shiftedHankelTailQuadratic_le_frobeniusBudget` proves the exact
  Frobenius budget
  `F_d(eta) = sqrt(sum_{i,j} eta_(i+j+1)^2)` from entrywise tail bounds.
- `abs_shiftedHankelTailQuadratic_le_rowSumBudget` proves the real-symmetric
  Schur/row-sum alternative with the literal finite maximum
  `G_d(eta) = max_i sum_j eta_(i+j+1)`.
- `finiteDegreeShiftedHankel_posDef_of_lambdaMin_margin` proves the paper
  disjunction `lambda_min(B_d) > F_d(eta)` or
  `lambda_min(B_d) > G_d(eta)` without replacing either branch.
- `finiteDegreeShiftedHankel_principal_det_pos_of_lambdaMin_margin` proves
  positivity of every principal determinant, including the full determinant.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/FiniteDegreeShiftedHankelTailStability.lean`
  — clean.
- `lake build GaloisForLFunctions.HTGeometry.FiniteDegreeShiftedHankelTailStability`
  — green.
- `#print axioms` for the two literal-gate capstones and both tail estimates:
  `[propext, Classical.choice, Quot.sound]` only.

## Scope boundary

This certifies exactly the finite linear-algebra gate. It supplies no actual
RH bulk matrix, tail moments, or strict margin, so it does not assert RH or a
height range without those independently certified inputs.
