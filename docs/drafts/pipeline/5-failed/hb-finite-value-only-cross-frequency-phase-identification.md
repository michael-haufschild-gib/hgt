# Failed route: finite value-only cross-frequency HB phase identification

- **ID:** HB-FINITE-CROSS-ALLPASS
- **Stage:** 5-failed
- **Status:** KILLED IN LEAN
- **Date:** 2026-08-31

## Failed claim

A finite symmetric packet of physical-frequency response values can determine the causal
Schwarz-real all-pass phase needed to derive FE/minimum-phase clock covariance.

## Exact killing mechanism

For every nonempty finite symmetric sample set, the formal theorem
`not_hbFiniteCrossFrequencyValueAllPassUnique` constructs a nonconstant causal Schwarz all-pass
multiplier equal to one at every sample. It remains invisible to every observable that factors
through the finite value vector, while its boundary logarithmic phase clock is strictly positive
at every frequency.

Thus adding more finitely many cross-frequency values, or applying arbitrary nonlinear
post-processing to them, cannot repair this producer class.

## Strongest positive survivor

Finite values fail, but the proof isolates four data types not erased by the obstruction:

- a confluent frequency derivative/jet;
- an infinite uniqueness set;
- a time-bilocal external phase reference;
- a literal-source global minimum-phase or winding theorem.

These are not optional refinements. At least one is logically required before the HB chain can
reach source-clock defect extinction.

## New insight

Strict squarefree Laguerre positivity is the exact physical orientation invariant behind the
obstruction. It simultaneously prevents real-axis pole collisions and forces strictly positive
clock. Schwarz symmetrization preserves upper-half-plane holomorphy and adds the two oriented
clocks, so physical FE reality does not rescue finite-sample identifiability.

## Paper and Lean status

Dependency-closed paper proof and unconditional Lean proof complete in
`GaloisForLFunctions.RHTower.HBFiniteCrossFrequencyCausalSchwarzAllPassNoGo`.

