# Scale-invariant source orientation cannot pay budget — Lean certificate

- **ID:** `scale-invariant-source-orientation-cannot-pay-budget-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `scale-invariant-source-orientation-cannot-pay-budget.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`GaloisForLFunctions.RHTower.SourceNormalizationBudgetGates`
(umbrella: `GaloisForLFunctions.RHTower`).

## Exact certificate

`GaloisForLFunctions.source_orientation_fixed_budget_forces_posSemidef`
proves that every residual in a class closed under all positive real rescalings
is positive semidefinite whenever adding each residual to one fixed budget is
positive semidefinite. It also exposes the one-sided ray form as
`source_budget_one_sided_recession_posSemidef`.

The result is over arbitrary real modules and real bilinear forms, stronger
than the card's finite-dimensional setup. No source-specific or RH premise is
introduced.

## Verification

- Targeted leaf build:
  `lake build GaloisForLFunctions.RHTower.SourceNormalizationBudgetGates`.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
