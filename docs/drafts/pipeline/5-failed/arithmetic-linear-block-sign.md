# Blockwise negativity is too strong even at constant phase speed

- **Stage:** 5-failed
- **Type:** FALSIFIED (Lean), limited model claim
- **Rejected statement:** every complete turn of `b(x)sin(lambda*x)` is nonpositive when `0<lambda<2*pi`, where `b(x)=(fract(x)^2-fract(x))/2`.

## Exact obstruction

At `lambda=4*pi/3`, Lean proves the second turn's integral over `[3/2,3]` is strictly positive (`linearPhase_second_turn_pos`). This uses the actual periodic quadratic, with no perturbed coefficients or computed constants.

This formal no-go concerns the constant-speed model. The separate B1 conjecture for the logarithmic remainder has verified numerical counterevidence; this card does not claim its analytic/Lean refutation.

## Strongest positive survivor

For every `0<lambda<2*pi` and every `A>=0`, the entire prefix `integral_(0..A)b(x)sin(lambda*x) dx` is nonpositive. Its complete-turn value is an exact function of the fractional endpoint and is zero exactly at integer endpoints. The positive second turn restores the negative first prefix exactly to zero.

This is a sign theorem and an exhaustive equality classification, not just the negation of blockwise negativity. Its closed paper proof and eleven Lean theorems are in [the formal certificate](../3-formalized/arithmetic-linear-phase-prefix.md).

## Consequence and limit

A whole-prefix proof must retain the initial negative contribution when later turns are positive. It cannot reset the same sign claim at every turn. The exact equality cases also prevent transfer through a perturbation argument that assumes a uniform strictly negative margin.

The corresponding logarithmic phase law remains open, as does the independent arithmetic constraint at the unit term of every zero. Neither follows from this model theorem; RH remains unproved.
