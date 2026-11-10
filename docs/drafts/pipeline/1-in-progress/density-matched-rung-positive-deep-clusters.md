# Density-matched positive windows with infinitely many deep zeros

- **ID:** A105
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** For every fixed aperture `a>0` and depth `0<δ≤1/2`, construct a tempered
  configuration positive on that window, with zeros of depth `δ` at unbounded heights,
  and counting function differing from zeta's by `O(T)`.

## Construction

Use the off-line lattice pair `{1/2±δ+2πik/L}` with `L≥2a`. Poisson summation gives
`W(f,f)=2L ||f||²` on the aperture, independently of depth. Add the critical projection
of zeta's divisor: it contributes a nonnegative form and exactly zeta's ordinate counts.
The lattice adds at most `(L/π+2)(T+1)` zeros through height `T`, hence `o(T log T)`.
It supplies zeros of depth exactly `δ` above every height.

## Remaining mathematical obligations

Assemble positivity, temperateness, the linear lattice count, and zeta-density transfer.

The aperture is fixed before choosing the configuration. Positivity for one fixed
configuration on an unbounded sequence of full windows would imply positivity on
every compact test, a different assertion.
