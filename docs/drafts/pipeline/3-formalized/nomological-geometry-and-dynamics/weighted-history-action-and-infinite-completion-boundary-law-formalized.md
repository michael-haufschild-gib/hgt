# Lean formalization: weighted history action and infinite completion boundary

- **Source card:** `weighted-history-action-and-infinite-completion-boundary-law.md`
- **Formalization date:** 2026-08-28
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NOT RH]`

## Modules

| Module | Formalized content |
|---|---|
| `GaloisForLFunctions.HTGeometry.NomologicalThreeOrganIndependenceLaw` | Logical independence of descent, symbol conservativity, and relative inf-compactness; scalar polynomial no-go |
| `GaloisForLFunctions.HTGeometry.WeightedHistoryCompletionBoundaryLaw` | Dense finite-support histories, compact completion, finite/compact action sublevels, subadditivity, exact boundary relaxation |

Both modules are reachable from the project umbrellas.

## Paper-to-Lean map

- Proposition 2.1:
  `nomological_three_organ_logical_independence`.
- Three-rank scalar-law calibration:
  `polynomial_eq_zero_of_eval_natCast_eq_zero`,
  `scalar_three_rank_polynomial_no_go`.
- Theorem 3.1 and supporting infrastructure:
  `weightedHistoryAbstractCompletion`, `weightedHistoryCompactAbstractCompletion`,
  `weightedHistoryAction_sublevel_finite`, `weightedHistoryAction_add_le`,
  `weightedHistoryRelaxation_eq_action`,
  `weightedHistoryRelaxation_eq_top_of_not_mem_range`,
  `weightedHistory_completion_boundary_law`,
  `binaryWeightedHistory_completion_boundary_law`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/NomologicalThreeOrganIndependenceLaw.lean`
  passed.
- `lake env lean GaloisForLFunctions/HTGeometry/WeightedHistoryCompletionBoundaryLaw.lean`
  passed.
- Both corresponding targeted `lake build` module commands passed; no umbrella build was run.
- Declarations pre-existed this promotion, so no redundant axiom audit was repeated.

Section 6 of source card is a conjectural source-transgression construction. It is preserved as
conjectural and excluded from formalization claim.
