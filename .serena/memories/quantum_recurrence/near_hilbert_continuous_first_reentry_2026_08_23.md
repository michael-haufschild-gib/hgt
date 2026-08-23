Closed C9/C10 for universal quantum recurrence project.

- Added `HTGeometry/NearHilbertContinuousCircuitEntropyLaw.lean`: eventual fixed-error entropy exclusion for continuous two-qubit circuits up to `2^n / (64*(n+1))` gates.
- Added `RHTower/NearestNeighborNearHilbertContinuousCircuitSameDrawLaw.lean`: one ordinary static nearest-neighbor Gaussian draw combines laboratory ramp, syndetic fixed-error hard intervals at near-Hilbert budget, and permanent locality/Haar separation.
- Added `HTGeometry/UniformProjectiveContinuousCircuitFirstReturnLaw.lean`: compact full continuous circuit image gives genuine consecutive visit gaps, preserving actual circuit endpoints rather than net points.
- Added `RHTower/NearestNeighborNearHilbertContinuousCircuitFirstReturnLaw.lean`: same draw has arbitrarily late genuine exit/re-entry episodes relative to entire phase-saturated continuous circuit image.
- All four modules pass `lake env lean` and targeted `lake build`; headline axioms are only `propext`, `Classical.choice`, `Quot.sound`.
- Wired into `HTGeometry.lean` and `RHTower.lean`; no umbrella build.
- Global lint only fails pre-existing unreachable `GaloisForLFunctions.RHTower.CesaroSignRecurrence`.
- Honest remaining core: initial post-ramp plateau and system-size lower bound on first re-entry/episode width. Current C10 is arbitrarily late consecutive re-entry, not global initial first return.
- No git actions. No stale Lean/lake processes.