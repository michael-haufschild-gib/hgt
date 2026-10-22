# Intrinsic theta C5 minima force normalized-flux log-concavity

- **ID:** `C5-FLC1`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE CLASSIFICATION (Lean)
- **Source:** `docs/drafts/pipeline/5-failed/theta-cusp-c5-stationary-flux-logconvexity.md`
- **Statement:** Every negative local minimum of intrinsic source C5 forces strict negativity of
  the second squared-coordinate derivative of `log(D(sqrt x)/sqrt x)`, with an exact
  sum-of-negative-terms certificate.

## Lean artifact

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureIntrinsicFluxLogConcavity`
- Exact certificate:
  `RHTower.stationary_c5_fluxLogCurvature_certificate`
- Calculus bridge:
  `RHTower.hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFlux`,
  `RHTower.hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFluxSlope`, and
  `RHTower.hasDerivAt_thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogSlope`
- Main sign theorem:
  `RHTower.thetaCuspReflectedSourceSquaredNormalizedDecayFluxLogCurvature_neg_of_intrinsicBalance_localMin_neg`
- Failure classification:
  `RHTower.thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_normalizedFluxLogCurvature_neg`
- Exact remaining burden:
  `RHTower.thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_intrinsicMin_normalizedFluxLogCurvature_nonneg`
- Closed no-go:
  `RHTower.not_exists_thetaCuspReflectedSource_intrinsicBalance_localMin_neg_and_normalizedFluxLogCurvature_nonneg`

## RH-chain consequence

Stationary/projective local flux-log-convexity is retired as an independent route to `C5-RB1`:
the exact negative-witness algebra forces strict log-concavity. Surviving significant premise is a
theta-specific nonlocal exclusion of this quantified chamber. That premise would close
modular-center C5 before still-open off-center rank-four, higher-packet/no-escape, and
CLG/TTF-or-Weil joins to RH.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspFifthRootCurvatureIntrinsicFluxLogConcavity.lean`
- targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureIntrinsicFluxLogConcavity`
- `#print axioms` on exact certificate, main sign theorem, failure classification, iff reduction,
  and closed no-go
- formal lint gate

All audited declarations use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
No conjectural premise, added axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation occurs.
