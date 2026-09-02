# Vacuum-index cancellation and determinant-family torsion — Lean certification

- **ID:** `ULF-CIT-1`
- **Stage:** 3-formalized
- **Paper card:** `completion-index-transgression-mechanics/vacuum-index-cancellation-determinant-torsion.md`
- **Lean module:** `GaloisForLFunctions.RHTower.VacuumIndexCancellationDeterminantTorsion`

## Certified declarations

- `ker_comp_eq_of_injective`: injective completion preserves the exact kernel.
- `earlierCokerToCompositeCoker_injective_of_injective`: canonical earlier-cokernel map is
  injective.
- `injectiveComposition_cokernel_exact`: full short-exact cokernel package plus kernel identity.
- `finrank_coker_comp_eq_of_injective`: exact finite-dimensional cokernel dimension law.

## Verification

Direct `lake env lean` check and targeted `lake build` passed. Targeted axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean` and
`HTGeometry.UniversalLawField`; no umbrella build was run.
