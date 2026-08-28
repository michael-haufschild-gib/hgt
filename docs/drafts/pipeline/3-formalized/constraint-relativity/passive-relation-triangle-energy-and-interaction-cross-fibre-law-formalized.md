# Lean formalization: passive relation triangles and interaction cross-fibres

- **Source card:** `passive-relation-triangle-energy-and-interaction-cross-fibre-law.md`
- **Formalization date:** 2026-08-28
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NOT RH]`

## Modules

| Module | Formalized content |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PassiveRelationTriangle` | Selected holonomy, leakage/work identities, quantitative energy law, zero criterion, asymptotic decay |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PassiveRelationPhaseWitness` | Positive-leakage phase non-identifiability witness |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition` | Partial traces and scalar/local/cross decomposition |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.InteractionCrossFibre` | Complex interaction cross-fibre, normalizer, two-qubit witness |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PassiveRelationHermitianCrossFibre` | Exact Hermitian cross-fibre, boundary kernel, orthogonal splitting, normalizer, finrank |

All modules are reachable from `GaloisForLFunctions.HTGeometry`.

## Paper-to-Lean map

- Proposition 2.1:
  `gaugeTransport_selectedHolonomy`, `gaugeTransport_leak_norms_and_work`.
- Theorem 3.1:
  `omega_eq_transported_leaks`, `work_eq_norm_sq_sub_norm_sq_holonomy`,
  `work_eq_two_re_inner_omega_sub_norm_sq`, `norm_omega_sq_le_three_mul_work`,
  `selectedHolonomy_eq_iff_leaks_eq_zero`, `omega_tendsto_zero_of_leaks`.
- Theorem 3.5:
  `positiveLeakage_not_determine_phase` and its explicit phase-witness lemmas.
- Theorem 5.1:
  `hermitianMatrixCrossFibre_eq_hermitianTracelessKroneckerSpan`,
  `normalizedHermitianBoundaryMap_mem_hermitianTracelessMatrices`,
  `ker_normalizedHermitianBoundaryMap`,
  `hermitianJointTraceless_eq_local_sup_cross`,
  `hermitianMatrixLocalReporter_inf_hermitianMatrixCrossFibre_eq_bot`,
  `hsInner_eq_zero_of_mem_hermitianCross_of_mem_hermitianLocal`,
  `finrank_hermitianMatrixCrossFibre`.
- Theorem 5.2:
  `preserves_hermitianMatrixLocalReporter_iff_localForm`.
- Corollary 5.3:
  `twoQubit_ZZ_exposure`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/PassiveRelationHermitianCrossFibre.lean`
  passed.
- `lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.PassiveRelationHermitianCrossFibre`
  passed; no umbrella build was run.
- `#print axioms` for the eight newly introduced Hermitian capstones reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Formal lint found no proof-debt or wiring defect in this module.

No theorem assumes the desired conclusion. No `sorry`, `admit`, project `axiom`, `opaque`, or
`unsafe` declaration is used.
