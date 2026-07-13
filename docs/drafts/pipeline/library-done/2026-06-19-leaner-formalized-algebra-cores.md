# Library update request — additional formalized algebra-core cards

- **Date:** 2026-06-19
- **From:** Leaner
- **Requested ledger action:** add/update formalization ledger entries for four new `3-formalized` algebra-core cards.

## New formalized cards
- `docs/drafts/pipeline/3-formalized/rank-two-unipotent-curvature-identity.md`
  - Lean file: `formal/GaloisForLFunctions/HTGeometry/CrossPrimeCurvature.lean`
  - Theorems: `upperUnipotentE_mul`, `upperUnipotentE_curvature_eq`
  - Split from `cross-prime-curvature-reducibility.md`.
- `docs/drafts/pipeline/3-formalized/two-prime-gluing-witness.md`
  - Lean file: `formal/GaloisForLFunctions/RHTower/GluingWitness.lean`
  - Main theorem: `gluing_per_prime_same_but_joint_distinct`
  - Split from `c3-gluing-invariants-bridge.md`.
- `docs/drafts/pipeline/3-formalized/finite-orbit-balance-algebra.md`
  - Lean file: `formal/GaloisForLFunctions/HTGeometry/OrbitBalance.lean`
  - Theorems: `orbitDegree_zero`, `orbitDegree_single`, `orbitDegree_add`, `orbitDegree_sub`, `orbitDegree_single_sub_single`, `eq_sum_single_sub_base_of_orbitDegree_zero`, `orbitDegree_intShiftCoboundary`, `sum_intShiftTerm_right`
  - Split from `two-sources-of-hypertranscendence.md`.
- `docs/drafts/pipeline/3-formalized/function-field-degree-collapse-core.md`
  - Lean file: `formal/GaloisForLFunctions/RHTower/FunctionFieldDegeneration.lean`
  - Theorems: `ffDegreeMap_apply`, `ffRelationLattice_mem_iff`, `ffDegreeMap_surjective`, `ffDegreeMap_range_eq_top`, `ffRelationLattice_corank_eq_one`
  - Split from `function-field-holonomicity-degeneration.md`.

## Note
The parent cards remain in `2-fully-proven`; these new cards cover exact subclaims whose whole stated content is now Lean-formalized and axiom-audited.
