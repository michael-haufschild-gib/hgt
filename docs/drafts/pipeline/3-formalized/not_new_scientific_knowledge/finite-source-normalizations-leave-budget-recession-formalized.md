# Finite source normalizations leave budget recession — Lean certificate

- **ID:** `finite-source-normalizations-leave-budget-recession-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `finite-source-normalizations-leave-budget-recession.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`GaloisForLFunctions.RHTower.SourceNormalizationBudgetGates`
(umbrella: `GaloisForLFunctions.RHTower`).

## Exact certificates

- `sourceNormalizationAffine_add_smul_recession` proves that all real multiples
  of a normalization-invisible direction remain in the exact affine source
  class.
- `finite_source_normalizations_budget_force_recession_zero` proves the
  stronger two-sided result: every such direction is identically zero.
- `finite_source_normalizations_budget_force_recession_posSemidef` is the
  card's stated Loewner-cone conclusion.

The normalization index type is arbitrary, hence includes every finite list.
No finite-dimensionality, scale estimate, or RH assertion is assumed.

## Verification

- Targeted leaf build:
  `lake build GaloisForLFunctions.RHTower.SourceNormalizationBudgetGates`.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
