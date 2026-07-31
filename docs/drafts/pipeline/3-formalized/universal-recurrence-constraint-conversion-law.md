# Universal recurrence constraint-conversion law

- **ID:** `universal-recurrence-constraint-conversion-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/UniversalRecurrenceConstraintConversionLaw.lean`

## Exact law

For every finite real spectrum, a projective character is fixed almost
surely by the unique completed-time phase law exactly when its balanced
integer coefficient function is an exact spectral relation. The same
character is detected by the resolved replica hierarchy exactly at its
positive coefficient mass.

Writing \(C_E\) for the rational span of all exact balanced relations and
\(\tau_E\) for the operational dimension of the completed phase law,
\[
  \boxed{
  \tau_E+\dim_{\mathbb Q}C_E
  =
  \dim_{\mathbb Q}P_E,}
\]
where \(P_E\) is the complete projective character carrier.

Thus completed recurrence, exact spectral arithmetic, operational temporal
dimension and resolved replica detection are four descriptions of one
projective constraint object.

## Formal declarations

- `relationPhaseEnsemble_constraint_iff`;
- `relationPhaseEnsemble_constraintSpace_eq`;
- `relationPhaseEnsemble_constraint_iff_detected`;
- `relationPhaseEnsemble_resolvedReplica_iff`;
- `phaseLawTemporalDimension_add_constraintRank`;
- `relationPhaseEnsemble_temporalDimension_add_relationRank`.

## Verification

Target source compilation with cached output passes:

```text
lake env lean GaloisForLFunctions/HTGeometry/UniversalRecurrenceConstraintConversionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/UniversalRecurrenceConstraintConversionLaw.olean
```

Axiom audit of all load-bearing declarations reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque` or `unsafe` declaration is
used. Final `lake build` module audit is reserved for publication audit.
