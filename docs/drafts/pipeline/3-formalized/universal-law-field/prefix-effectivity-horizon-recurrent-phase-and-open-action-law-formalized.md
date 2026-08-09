# Prefix effectivity horizon law — Lean certification

- **Card:**
  `prefix-effectivity-horizon-recurrent-phase-and-open-action-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveEffectivityHorizon`
- **Source:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveEffectivityHorizon.lean`
- **Status:** `[LEAN-PROVED] [NO PROJECT AXIOMS] [NO COMPUTATION PROOF]`

## Certified declarations

- `constitutivePrefixObservation_eq`
- `constitutivePrefixObservation_stable`
- `finiteLawProfile_constitutivePrefixHistory_eventually_allTrue`
- `constitutivePrefixHistory_production`
- `constitutivePrefixHistory_card`
- `constitutivePrefixPhase_period_two`
- `constitutivePrefixPositiveShadow_eq_one`
- `constitutivePrefix_simultaneous_closedObservation_openAction`
- `constitutivePrefix_effectivityHorizon_law`

The final theorem is a closed conjunction of finite observer stabilization, pointwise convergence to
the already-certified non-effective all-true profile, singleton production, exact cardinal action,
period-two phase, positive phase erasure, and arbitrarily large action at simultaneous observer and
phase returns.

## Verification

- foreground `lake env lean` on the source module passed;
- final `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passed;
- `#print axioms` reports only standard quotient/extensionality/classical-choice dependencies;
- no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, or computation proof occurs in module.
