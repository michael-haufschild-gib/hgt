# FZZ-P asymptotic matching from stabilized diagonal flow

- **ID:** FZZ-P-HC6-NG
- **Stage:** 5-failed
- **Type:** SHARP DYNAMICAL NO-GO WITH POSITIVE SURVIVOR
- **Route:** Use long-time evolution of the HC5 source-gap stabilized finite block to preserve the
  diagonal reflection reporter and force critical-line matching.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityDiagonalFlowDetectorHorizon`

## Failed premise

HC5 supplies a canonical, source-native generator with real spectrum at every positive scale.  One
might expect its exact evolution to preserve the diagonal energy's critical-line detection and make
equilibrium or late-time reflected matching a spectral consequence.

## Exact killing theorem

The evolved diagonal energy has coefficients

`(k_beta(t)^2,-k_beta(t),0,1)`,

where `k_beta(t)=(Q/R)(exp(Pt)-1)`.  Its universal reciprocal-radius separation holds at
nonnegative time exactly when

`t<=T_beta=log(1+R/Q)/P`.

The horizon is finite and positive.  Every later time leaves HC3's sharp detector cone, hence a
blind off-unit reflected pair exists.  Real spectrum of the generator therefore does not protect
the reporter under asymptotic evolution.

## Strongest positive survivor

The failed route exposes an exact maximal validity law:

- closed rank-one semigroup and polynomial functional calculus;
- exact pullback parabola for diagonal energy;
- finite source-defined detector horizon;
- survival on the lightlike boundary;
- pointwise Mellin critical-line equivalence throughout the entire closed time window;
- strict post-horizon phase blindness.

Paper proof and unconditional Lean formalization are complete in
`../3-formalized/fzz-p-diagonal-flow-detector-horizon.md`.

## New insight

Local spectral stability is dynamically insufficient in a stronger sense than HC5 established:
even the detector-generating energy itself escapes the reflection cone under the exact stabilized
flow.  Any surviving FZZ/GFZZ mechanism must prevent cone escape, periodically reset the reporter,
or add mode-sensitive nonlocal structure.  Pure late-time relaxation of this finite source block is
retired.

## Status

- exact no-go and positive survivor proved on paper;
- all flow, cone-crossing, and Mellin-window claims formalized in Lean;
- direct Lean, targeted build, forbidden-token scan, diff check, and axiom audit passed;
- literature search found no exact collision; independent priority audit remains.

## Log

- 2026-08-28 — Asymptotic stabilized-flow matching retired after exact finite detector horizon;
  positive survivor formalized before retirement.
