# FZZ momentum-fitted radial/compact cancellation

- **ID:** FZZ-P-MFRCW
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** Existential factorized radial/compact mixed Ward cancellation cannot select zero momentum.

## No-go closure

- **Exact killing theorem/mechanism:** `fzzMomentumFittedRadialCompactWardRouteKilled`; compact cross-charge response is linear with nonzero coefficient, so one unique cancelling separation exists for every momentum.
- **Strongest positive survivor:** `fzzRadialCompactMixedWardDefect_eq_zero_iff` classifies exact cancelling separation; `fzzRadialCompactMixedWardDefect_zeroMomentum_eq_zero_iff` shows zero momentum requires zero relative separation.
- **New insight:** Geometry must be source-fixed independently of momentum. Allowing target-fitted annulus motion makes Ward cancellation universal.
- **Status:** Paper proof closed; Lean module wired into `RHTower.lean`; direct check, targeted leaf build, standard-axiom audit, lint, and whitespace check passed. Full neutral source and independent phase-frame identity remain open.
