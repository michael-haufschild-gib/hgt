# Theta C5 stationary-locus reduction (2026-08-29)

Formalized `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryLocus` and wired it into `RHTower.lean`.

New exact velocity: `C5Velocity = 39*A*D + t*A*J - 17*t*D^2 + t^2*(5*A*K - 3*D*J)`, where `K = dJ/dt = P*(q3 - 3*q1*q2 + q1^3)`.

Using corpus strict C5 near zero, newly proved strict cofinal tail C5, compact minimization, and Fermat, Lean proves every modular-center C5 failure has a positive-radius negative stationary witness. Main theorems:
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_neg`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_taxOverspend`
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_taxReserve`

Open conjecture `C5-SL1` is now precisely: at every `t>0` with `C5Velocity(0,t)=0`, likelihood tax density is at most integral chord reserve. It comes from corpus exact chord-reserve identity + seam/tail positivity and is equivalent to all-radius center C5.

Downstream chain: C5-SL1 -> modular-center C5 -> open off-center/complement transport -> global source C5 -> odd rank-four wall -> physical center-mixed rank four -> open higher packets/cofinal no-escape -> universal tilt-flux or Xi-Weil positivity -> RH.

Verification: direct `lake env lean` clean; targeted leaf `lake build ...StationaryLocus` passed; axiom audit only `[propext, Classical.choice, Quot.sound]`. Lint sees module as reachable; repo-wide lint still fails only on pre-existing unrelated unreachable modules. Frontier map was not edited.