# Divisor recovery at polynomial damping scales

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Statement

For an actual finite exceptional packet, some `A>0` should recover every
selected isolated zero with radius `y(t)=t^(−A)` and angle `−π/2+1/t`.
The normalized divisor limit should hold for every eventually positive
spacing `h(t)→0`, retaining the full complementary divisor.

## Proposed derivation

The boundary contour and reciprocal-mode estimates are uniform in the
exponential speed `a`. Substitute `a(t)=A log(t)/t`. On a regular line
`σ<c<Re ρ`, their product bounds the normalized remainder by

`CD t^(N+M−A(Re ρ−c)/2)`.

Thus `A(Re ρ−c)/2>N+M` suffices. This is a uniform diagonal argument;
the fixed-speed limit alone does not justify it. Kernel nonvanishing must
also be supplied independently of fixed-speed mode growth.

The real part of the damping is of order `t^(−A−1)`, so its effective
prime cutoff is polynomial in height, of order `t^((A+1)/2)`. This may
permit arithmetic estimates unavailable at the earlier exponential cutoff.
No prime cancellation estimate at this scale is claimed.

## Status

Corpus search found fixed exponential-speed receivers but no corresponding
polynomial-radius theorem. The boundary-contour and fixed-speed recovery
modules now pass direct source audits; see
`../3-formalized/b13-boundary-damping-recovers-exceptional-divisor.md`.
The proposed varying-speed limit, kernel nonvanishing and cutoff comparison
remain to be formalized.
