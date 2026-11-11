# Density-matched positive windows with infinitely many deep zeros

- **ID:** A105-fixed-aperture-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For every fixed aperture `a>0` and depth `0<δ≤1/2`, construct a tempered
  configuration positive on that window, with zeros of depth `δ` at unbounded heights,
  and counting function differing from zeta's by `O(T)`.

## Construction

Use the off-line lattice pair `{1/2±δ+2πik/L}` with `L≥2a`. Poisson summation gives
`W(f,f)=2L ||f||²` on the aperture, independently of depth. Add the critical projection
of zeta's divisor: it contributes a nonnegative form and exactly zeta's ordinate counts.
The lattice adds at most `(L/π+2)(T+1)` zeros through height `T`, hence `o(T log T)`.
It supplies zeros of depth exactly `δ` above every height.

## Lean

`SelectiveArithmetic/TheRungSignSurvivesDeepZerosAtZetaDensity.lean` contains
`exists_zetaDensity_positive_window_deep_zeros`. Direct check passed; module wired.

## Quantifier boundary

For one tempered configuration and any aperture law `r(T)→∞`, eventual full-window
positivity is equivalent to all zeros lying on the critical line. A finite onset
aperture contradicts the unbounded law; infinite onset is exactly criticality.
`onLine_iff_positive_along_unbounded_apertures` formalizes this boundary and passes
the same direct check.

Thus a single configuration with deep zeros cannot satisfy a growing full-window
rung. The positive survivor fixes the aperture before choosing the configuration:
it preserves zeta's leading density and has infinitely many fixed-depth zeros.
Positivity restricted to a smaller packet class is a separate question.
