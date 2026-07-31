# Separable-interaction temporal-dimension law

- **ID:** `separable-interaction-temporal-dimension-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/SeparableInteractionTemporalDimensionLaw.lean`

## Theorem

For every pair of nonempty finite spectra, a single factorized diagonal
interaction
\[
  E_{ab}=E^A_a+E^B_b+x_a y_b
\]
can be chosen arbitrarily small so that the coupled spectrum has maximal
projective temporal dimension.

If the factors have \(m+1\) and \(n+1\) levels, respectively, then:

\[
  \tau_{\rm uncoupled}\le m+n,\qquad
  \tau_{\rm coupled}=mn+m+n,
\]
so the temporal-dimension gain is at least \(mn\). The interaction has
operator-Schmidt rank one. The same witness obeys the operator-norm
Hamiltonian-distance bound, the dimension-free fixed-time Heisenberg-probe
bound and every positive full-support replica collision floor.

## Interpretation boundary

Operator-Schmidt rank one is a genuine separability restriction, but it is
not geometric locality inside either factor. The diagonal factors may be
global functions of each block's energy basis. Spatial locality requires a
separate microscopic realization.

## Verification

Target compilation passes:

```text
lake env lean GaloisForLFunctions/HTGeometry/SeparableInteractionTemporalDimensionLaw.lean
```

Axiom audit reports only `propext`, `Classical.choice` and `Quot.sound`.
Final `lake build` module audit is reserved for publication audit.
