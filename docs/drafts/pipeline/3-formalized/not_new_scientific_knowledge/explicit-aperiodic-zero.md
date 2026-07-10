# Explicit aperiodic zero discharges finite-clock escape

- **ID:** explicit-aperiodic-zero
- **Stage:** 3-formalized
- **Type:** NOT-NEW / INTERFACE DISCHARGE
- **Source:** RHTower `PeriodicityDichotomy` + `ClockEscape`
- **Statement:** `[PROVED]` The linear carrier `z ↦ z-ρ` has an aperiodic zero at `ρ`. For the constant approximating family and singleton clock inventory `{1}`, the finite-clock escape conclusion is unconditional.

## Proof

The carrier vanishes at `ρ`.  If it vanished at every point of a positive vertical progression,
the `k=1` member would give `T=0`, contradicting `T>0`.  Thus it supplies
`AperiodicZeroAt` without hypotheses.  The constant family converges locally uniformly to itself;
the whole plane is shift-closed; the linear carrier is continuous; and the only inventory period
is positive.  These concrete providers discharge every premise of `aperiodic_zero_clock_escape`.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ExplicitAperiodicZero.lean`
- Provider: `simpleZeroAt_aperiodicZeroAt`
- Consumer capstone: `simpleZeroAt_singleClock_escape`
- Build: `lake build GaloisForLFunctions.RHTower.ExplicitAperiodicZero` PASS
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
