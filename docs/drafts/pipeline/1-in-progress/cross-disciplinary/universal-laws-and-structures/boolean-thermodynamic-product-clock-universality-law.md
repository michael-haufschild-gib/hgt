# Boolean--thermodynamic product-clock universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; LITERATURE AUDITED]`

## Lean-derived conjecture

Reading the terminal Boolean clock-holonomy law against the thermodynamic cycle-affinity law
exposes a product gauge group not represented in either endpoint.  On a connected graph:

- the order-two coordinate is globally exact exactly when the Boolean edge field has one XOR
  vertex orientation;
- the positive real coordinate is globally exact exactly when every closed thermodynamic
  affinity vanishes;
- the two conditions together should be exactly one global potential for the product-valued
  clock.

## Corpus inputs

- `GaloisForLFunctions.HTGeometry.exists_booleanOrientation_iff_clockCalibrationExact`
- `GaloisForLFunctions.HTGeometry.rateRatioCalibration_exact_iff_closedWalkAffinity_zero`
- `GaloisForLFunctions.HTGeometry.ClockCalibrationExact`

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof targeted searches covered graph cocycles, product gauge groups, Boolean
synchronization, cycle affinities, and detailed balance.  Nearby sources treat the two coordinate
mechanisms separately:

- Deaconu--Kumjian--Quigg, *Group actions on topological graphs*, arXiv:1007.2616, develops
  group-valued graph cocycles and skew-product graphs:
  <https://arxiv.org/abs/1007.2616>
- Polettini--Bulnes-Cuetara--Esposito, *Conservation laws and symmetries in stochastic
  thermodynamics*, studies graph topology, detailed balance, and thermodynamic affinities:
  <https://doi.org/10.1103/PhysRevE.94.052117>

Verdict: graph cocycles and the Wegscheider/detailed-balance cycle criterion are classical.  No
targeted source states the exact product-clock classification for a simultaneous
`Multiplicative (ZMod 2)` Boolean orientation and positive-real thermodynamic calibration.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/BooleanClockHolonomyUniversalityLaw.lean`

## Verification

- product-clock and thermodynamic proof core exact, warning-free:
  `lake env lean /tmp/hgt_law296.lean`
- Boolean source dependency exact, warning-free before integration:
  `lake env lean GaloisForLFunctions/HTGeometry/BooleanClockHolonomyUniversalityLaw.lean`
- source proof exact, warning-free after integration:
  `lake env lean GaloisForLFunctions/HTGeometry/BooleanClockHolonomyUniversalityLaw.lean`
- target module already imported by `GaloisForLFunctions/HTGeometry.lean`
- final module build deferred to terminal audit
