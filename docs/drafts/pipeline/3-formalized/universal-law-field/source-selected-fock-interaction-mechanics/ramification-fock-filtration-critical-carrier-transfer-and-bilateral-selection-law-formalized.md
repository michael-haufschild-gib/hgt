# Ramification Fock filtration and bilateral selection — Lean certification

- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveRamificationFockExcessSelection`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

| Card result | Lean |
|---|---|
| Theorem 2.1 — exact three-layer reconstruction | `ramificationFockMass`, `ramificationOneParticleMass`, `ramificationManyParticleMass`, `ramification_threeLayer_reconstruction` |
| §3 — analytic fusion and source-selected Fock response | `ramificationFockMass_pow`, `ramificationFockMass_eq_zero_of_not_mem_range`, `summable_ramificationFockMass_at_wall`, `summable_ramification_particleLayers_at_wall`, the nonnegativity and domination lemmas |
| Theorem 4.1 — prime and Boolean layers cannot carry the shell wall | `summable_ramificationInteractionMass`, `not_summable_ramificationInteractionMass_at_wall`, `ramificationCriticalCarrierClassification` |
| Theorem 5.1 — interaction properness selects the neutral grade | `BilateralInteractionAdmission`, `bilateralInteractionAdmission_iff`, `ramificationFockExcessSelection_capstone` |

## Verification (2026-08-20)

The module elaborates from the tree with 0 errors and every public declaration reports only
`propext`, `Classical.choice`, `Quot.sound`.  It is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.
