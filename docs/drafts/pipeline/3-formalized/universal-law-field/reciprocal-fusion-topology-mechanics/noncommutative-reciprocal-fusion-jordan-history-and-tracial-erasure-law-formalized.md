# Noncommutative reciprocal fusion, Jordan history, and tracial erasure — formalized

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/reciprocal-fusion-topology-mechanics/noncommutative-reciprocal-fusion-jordan-history-and-tracial-erasure-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveNoncommutativeReciprocalFusion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[FORMALIZED] [NO SORRY] [NO AXIOMS ADDED] [NOT RH]`

## Certified theorem surface

Lean proves unconditionally:

1. `reciprocalUnitWork_fusion` — ring-level direct/reflected congruence fusion;
2. `reciprocalCongruenceAction_commutator_decomposition` — exact radial plus commutator split;
3. `reciprocalCommutatorHistory_eq_zero_of_commute` and
   `reciprocalUnitWork_radial_fusion` — exact flat restriction;
4. `reciprocalCongruenceFusion_associator` — order-sensitive associator;
5. `reciprocal_congruence_eq_jordan_add_history` and
   `reciprocalUnitWork_jordan_fusion` — rational-algebra Jordan/double-commutator law;
6. `trace_reciprocalAdditiveCommutator` and
   `trace_reciprocalDoubleCommutatorHistory` — exact trace erasure;
7. `reciprocalHistoryWitnessRForm_pos`, `reciprocalHistoryWitnessQForm_pos`, and
   `reciprocalHistoryWitnessZForm_nonneg` — positive/semipositive witness forms;
8. `reciprocalHistoryWitnessRUnit`, `reciprocalHistoryWitnessQUnit`, and
   `reciprocalUnitWork_historyWitnessQ` — witness arises from genuine units and reciprocal work;
9. `reciprocalJordanHistory_witness_eq`, `reciprocalHistoryWitness_ne_zero`, and
   `trace_reciprocalHistoryWitness` — strict nonzero history with zero trace.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveNoncommutativeReciprocalFusion.lean
```

passed in foreground on 2026-08-12. The UniversalLawField umbrella imports the module; foreground
umbrella build passed (`11842` jobs). Scratch `#print axioms` on eight capstones reported only
`propext`, `Classical.choice`, and `Quot.sound`. Scoped forbidden-token scan found no `sorry`,
`admit`, `axiom`, `opaque`, or `unsafe` declaration.
