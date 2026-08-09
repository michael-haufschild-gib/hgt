# Formalized: Burnol divided shift / zero-evaluator separation

- **ID:** `burnol-divided-shift-evaluation-separation-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-divided-shift-evaluation-separation-law.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolDividedShiftEvaluationSeparation` | the five separation theorems |
| `GaloisForLFunctions.RHTower.BurnolDividedShiftSourceLeakage` | strict accretive source-leakage floor (input) |
| `GaloisForLFunctions.RHTower.GammaCoPoissonSoninActualZeroEscape` | zero evaluator lies in the source orthogonal (input) |

## Formal theorem chain

1. `burnolCoPoissonSourceProjection_evaluationVector_eq_zero_of_riemannZeta_eq_zero` — paper `(1)`:
   at a right-half-strip zeta zero the completed-Mellin evaluation vector has zero co-Poisson
   source projection.
2. `burnolCoPoissonSourceProjection_mellinDividedShift_sub_evaluationVector` — paper `(2)`:
   subtracting the evaluator does not change the divided shift's source projection.
3. `burnolMellinDividedShift_sub_evaluationVector_sourceProjection_lower_bound` — paper `(3)`:
   the retained source component still carries the full strict-accretive leakage floor
   `δ ‖A_w f‖² ≤ ‖f‖ ‖P_b(A_w f − k_{w,b})‖`.
4. `burnolMellinDividedShift_sub_evaluationVector_distance_lower_bound` — paper `(4)`, ambient form:
   `δ ‖A_w f‖² ≤ ‖f‖ ‖A_w f − k_{w,b}‖`, by contractivity of the orthogonal projection.
5. `burnolMellinDividedShift_ne_evaluationVector_of_riemannZeta_eq_zero` — paper `(4)`, non-landing:
   no nonzero co-Poisson source vector has divided shift equal to a zero evaluation vector.

No RH, critical-line placement, simplicity, source-flatness, or spectral hypothesis occurs in any
statement; the only hypotheses are the domain conditions `1/2 < Re w < 1`, `0 < b`,
`riemannZeta w = 0`, and membership in the closed source space.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/BurnolDividedShiftEvaluationSeparation.lean` — clean.
- `#print axioms` on all five theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions.RHTower`.
