# Anchored projective recurrence conservation law

- **ID:** `anchored-projective-recurrence-conservation-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveRecurrenceConservationLaw.lean`

## Exact law

For every nonempty finite real spectrum \(E:I\to\mathbb R\) and every
reference level \(r\in I\), let
\[
  V_{E,r}=\operatorname{span}_{\mathbb Q}
    \{E_i-E_r:i\in I\}.
\]
The projective detuning map on balanced rational characters has
\[
  \operatorname{im}\partial_E=V_{E,r},
  \qquad
  \ker\partial_E=L_E^{\mathrm{proj}}\otimes\mathbb Q.
\]
Consequently,
\[
  \boxed{
  \dim_{\mathbb Q}V_{E,r}
  +\dim_{\mathbb Q}(L_E^{\mathrm{proj}}\otimes\mathbb Q)
  =|I|-1.}
\]

This is reference-independent and avoids reindexing the spectrum by
`Fin`. Every projective character direction is exactly one temporal
direction or one exact recurrence constraint.

## Formal declarations

- `anchoredGapSubspace`;
- `anchoredTemporalRank`;
- `anchoredGapRationalCharacter`;
- `projectiveEnergyDetuning_anchoredGapCharacter`;
- `projectiveEnergyDetuning_range_eq_anchoredGapSubspace`;
- `anchoredTemporalRank_add_relationRank`.

## Verification

Direct target compilation passed with:

```text
lake env lean GaloisForLFunctions/HTGeometry/AnchoredProjectiveRecurrenceConservationLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/AnchoredProjectiveRecurrenceConservationLaw.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
