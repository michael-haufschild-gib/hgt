# Positive source weights do not bound Loewner budget — Lean certificate

- **ID:** `positive-source-weights-do-not-bound-loewner-budget-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `positive-source-weights-do-not-bound-loewner-budget.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`GaloisForLFunctions.RHTower.PositiveSourceLoewnerBudget`
(umbrella: `GaloisForLFunctions.RHTower`).

## Exact certificates

- `positiveSource_unbounded_budget_forces_zero`: for arbitrary source type
  `X`, any fixed real bilinear-form budget which Loewner-dominates every
  finitely supported nonnegative weighted sum of PSD source kernels forces
  every source kernel to be zero.
- `positiveSource_normalized_budget_iff`: for `C > 0` and PSD budget `B`, the
  budget for every nonnegative finitely supported weight of mass at most `C`
  is equivalent to `C • K x <= B` for every source point `x`.
- `normalizedSource_decomposition`: the exact Finsupp identity underlying the
  normalized implication; no finite-source-type reduction is used.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/PositiveSourceLoewnerBudget.lean`
  — clean.
- `lake build GaloisForLFunctions.RHTower.PositiveSourceLoewnerBudget` —
  green.
- `#print axioms` for both main certificates:
  `[propext, Classical.choice, Quot.sound]` only.

## Scope boundary

This proves the source-cone and source-budget guardrail. It supplies no
scale-sensitive estimate for the actual Euler/Gamma/functional-equation
residual, and therefore does not prove RH.
