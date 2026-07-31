# Universal projective recurrence capstone law

- **ID:** `universal-projective-recurrence-capstone-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean`

## Master object

For every finite real spectrum \(E=(E_0,\ldots,E_d)\), define the
projective detuning map
\[
  \partial_E:P_{\mathbb Q}\longrightarrow\mathbb R,
  \qquad
  \partial_E(q)=\sum_i q_iE_i,
  \quad \sum_iq_i=0.
\]

Its rational kernel is exactly the rational span \(C_E\) of all balanced
integer spectral relations. Its image is exactly the rational span \(V_E\)
of the anchored gaps \(E_i-E_0\). Hence
\[
  \boxed{\tau(E)+\dim_{\mathbb Q}C_E=d,}
\]
where
\[
  \tau(E)=\dim_{\mathbb Q}V_E.
\]

The operational temporal dimension of the unique completed-time phase law
is exactly this same \(\tau(E)\). Moreover, a projective character is fixed
almost surely by the completed law exactly when it belongs to the integer
relation lattice, and the resolved replica hierarchy sees it exactly at and
above its positive coefficient mass.

Thus completed recurrence measure, exact spectral arithmetic, operational
temporal dimension and replica observation depth are the kernel, image rank
and height filtration of one projective detuning map.

## Formal declarations

- `projectiveEnergyDetuningLinearMap`;
- `projectiveEnergyDetuning_ker_eq_relationSpace`;
- `projectiveEnergyDetuning_range_eq_gapSubspace`;
- `projectiveTemporalRank_add_relationRank`;
- `relationPhaseEnsemble_temporalDimension_eq_projectiveRank`;
- `finiteProjectiveRecurrence_universalLaw`.

## Verification

Target source compilation with cached output passes:

```text
lake env lean GaloisForLFunctions/HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.olean
```

Axiom audit of all load-bearing declarations reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque` or `unsafe` declaration is
used. Final `lake build` module audit is reserved for publication audit.
