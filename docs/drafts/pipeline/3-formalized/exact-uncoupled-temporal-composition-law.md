# Exact uncoupled temporal composition law

- **ID:** `exact-uncoupled-temporal-composition-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/TemporalDimensionInteractionMultiplicationLaw.lean`

## Exact law

Let \(V_A,V_B\subset\mathbb R\) be the rational spans of the anchored
energy gaps of two arbitrary nonempty finite spectra. For their uncoupled
tensor-sum spectrum,
\[
  \boxed{V_{A\boxplus B}=V_A+V_B.}
\]
Consequently its projective temporal dimension obeys exact
inclusion–exclusion:
\[
  \boxed{
  \tau(A\boxplus B)+\dim_{\mathbb Q}(V_A\cap V_B)
  =
  \tau(A)+\tau(B).}
\]
Equivalently,
\[
  \tau(A\boxplus B)
  =
  \tau(A)+\tau(B)-\dim_{\mathbb Q}(V_A\cap V_B).
\]

Thus the only failure of temporal-dimension additivity for uncoupled
composition is shared rational clock frequency. The earlier
\(\tau(A\boxplus B)\le \tau(A)+\tau(B)\) bound is a corollary.

## Formal declarations

- `bipartiteProduct_projectiveGapSubspace_eq`;
- `bipartiteProduct_temporalRank_add_sharedRank`;
- `bipartiteProduct_temporalRank_eq_sub_sharedRank`.

## Verification

Target source compilation with cached output passes:

```text
lake env lean GaloisForLFunctions/HTGeometry/TemporalDimensionInteractionMultiplicationLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/TemporalDimensionInteractionMultiplicationLaw.olean
```

Axiom audit reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque` or `unsafe` declaration is
used. Final `lake build` module audit is reserved for publication audit.
