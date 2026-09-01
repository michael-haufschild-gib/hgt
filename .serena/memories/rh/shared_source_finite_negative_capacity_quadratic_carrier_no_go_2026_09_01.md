# Shared source finite-negative-capacity no-go (2026-09-01)

Formalized `formal/GaloisForLFunctions/RHTower/SourceHorizontalFiniteNegativeCapacityQuadraticCarrierNoGo.lean`.

- `QuadraticFiniteNegativeCapacityAtMost Q k`: every injective finite-dimensional negative-definite landing into arbitrary-dimensional `Q` has dimension `≤ k`.
- Exact quadratic pullback preserves this bound: `sigNeg S ≤ k`.
- Right-half source packet size `m` forces target capacity `m-1`.
- Closed capstone `sourceHorizontalFiniteNegativeCapacityQuadraticCarrierRouteKilled`: off wall, packet size `max k₁ k₂ + 2` defeats simultaneous reflected landing into any pair of arbitrary-dimensional finite-capacity quadratic carriers.
- Positive survivor `sourceZeroHorizontalSharedReservoir_allPacketsLanding_forces_unboundedNegativeCapacity`: an all-packet linear quadratic carrier has no finite negative-capacity bound.
- Consequence: infinite ambient dimension is insufficient; shared HB/FZZ-P/PW-B/RBH linear-quadratic survivor must have genuinely infinite negative index, or be nonlinear/singular/domain-changing.
- Direct Lean, target `lake build`, and standard axiom audit passed. Wired into `RHTower.lean`. Global lint only reports unrelated concurrently unwired modules.
- Card: `docs/drafts/pipeline/3-formalized/source-horizontal-finite-negative-capacity-carrier-no-go.md`.
- Facts: `docs/drafts/pipeline/1-in-progress/rh-four-route-proof-graph-status.md`.