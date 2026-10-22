# Nomological geometry and dynamics — Stage-3 formalization program

- **ID:** `ngd-stage3-formalization-program`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `../2-fully-proven/nomological-geometry-and-dynamics/`
- **Statement:** Formalize every dependency-closed theorem in all eight Stage-2 cards without
  weakening source types, then wire, audit, and promote their Lean certificates.

## Goal

Close exact Lean coverage for descent/effectivity, odd Euler-comb admission, five-shadow
cancellation, polarized exactness, positive observer covariance, restricted-history saturation,
split-prime/inverse-monodromy no-go, and weighted-history completion.

## Gates

- [x] 0 → 1  in-progress: eight-card inventory and prior-corpus research completed
- [x] 1 → 2  fully-proven: source cards are already dependency-closed paper proofs
- [ ] 2 → 3  formalized: all named capstones pass direct Lean, axiom audit, lint, exact builds,
  and umbrella checks
- [ ] 3 → 4  publication-ready: out of scope

## Approach

Reuse exact corpus capstones first. Add only missing generic infrastructure and source wrappers.
Check each focused file with `lake env lean`; reserve `lake build <module>` for final audits. Keep
one foreground compiler/build process owned by this task.

## Current theorem map

- Polarized exactness: existing three-module implementation passes direct Lean and axiom audit.
- Robust polynomial saturation and Hurwitz differential matroid: existing exact capstones.
- Weighted history: dense subgroup completion, proper/nonclosed range, finite action sublevels,
  subadditivity, and infinite relaxed boundary implemented in
  `HTGeometry/WeightedHistoryCompletionBoundaryLaw.lean`.
- Three-organ independence/scalar no-go: implemented in
  `HTGeometry/NomologicalThreeOrganIndependenceLaw.lean`.
- Split-prime bounded shear: implemented in
  `HTGeometry/BoundedLogarithmicPrimeInfinityShear.lean`; existing divisor, inverse-monodromy, and
  coframe modules cover other algebraic components.
- Odd Euler comb: literal all-parameter `D'`, exact signed-measure admission threshold, admitted
  `S'` realization, endpoint variation, Route-L wall, and torque nonadmission implemented and
  promoted in `HTGeometry/OddEulerCombTemperedAdmissionWall.lean`.
- Descent, five-shadow, and remaining positive-observer source wrappers remain open.

## No-go closure

Not a falsified route. Negative source theorems retain their paper-card positive survivors and must
be promoted only with those survivors represented by named Lean capstones.

## Log

- 2026-08-13 — created after source/corpus inventory; weighted-history and three-organ modules pass
  direct focused checks.
- 2026-08-13 — odd Euler-comb card promoted to Stage 3 after direct Lean, exact leaf build, axiom
  audit, authoritative lint, and umbrella wiring.
