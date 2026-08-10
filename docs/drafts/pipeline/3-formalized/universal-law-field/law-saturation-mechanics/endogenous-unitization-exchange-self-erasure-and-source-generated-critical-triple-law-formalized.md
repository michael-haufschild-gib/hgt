# Endogenous unitization, exchange self-erasure, and source-generated critical triple — Lean certification

- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/law-saturation-mechanics/endogenous-unitization-exchange-self-erasure-and-source-generated-critical-triple-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveEndogenousUnitizationInterference`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]

## Certified theorem surface

Lean proves:

1. `executeFormationWord_eqvGen`: every formation-word endpoint lies in the equivalence closure of
   primitive unitization edges;
2. `executeFormationWord_endpoints_eqvGen`: any two word endpoints from one source point become
   equivalent;
3. `executeFormationWord_observer_unitized`: every observer unitizing the generators is constant on
   every word endpoint;
4. `joinedOperationUnitization_exchangePair` and
   `jointlyUnitizingObserver_erases_exchange`: joint execution collapses every exchange pair;
5. `endogenousDiracProfiles_conflict`, `endogenousDiracProfiles_totalVariation`,
   `finiteSignedFiberMass_endogenousDiracProfile`, and
   `endogenousDiracPushforward_totalVariation_zero`: the source-generated Dirac task is a canonical
   conflict with TV one and has observed TV zero after endpoint identification;
6. `endogenousExchangeReporter_exact_loss` and `endogenousExchangeReporter_strict_loss`: exact and
   strict reporter-balance forms;
7. `threePointLeftRetraction_idempotent`, `threePointRightRetraction_idempotent`, and the two schedule
   endpoint theorems: the source consists of two idempotent operations with noncommuting middle-state
   schedules;
8. `threePoint_sourceGenerated_pairwise_realizable` and
   `threePoint_sourceGenerated_no_joint_observer`: each unitization is individually lossless while
   no finite joint observer can retain the canonical schedule reporter;
9. `finTwo_pairwiseCompatible_joinCompatible`: two states cannot realize the same pairwise/joint
   incompatibility, proving state-minimality;
10. `endogenousUnitizationInterference_threePoint_closed`: bundled capstone.

## Verification

- Direct foreground elaboration:

  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveEndogenousUnitizationInterference.lean`

  passes.

- Formal lint passes with no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Final `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passes (11,522 jobs).
- Axiom audit reports no axioms for `executeFormationWord_eqvGen`,
  `executeFormationWord_observer_unitized`, and `joinedOperationUnitization_exchangePair`; the
  quotient, TV, pairwise-realizability, joint-impossibility, state-minimality, and bundled capstone
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope preserved

Formalization proves the strict observer-unitization sector.  It does not identify general descent
with unitization, construct an analytic admission lift, provide physical cost, or imply RH.
