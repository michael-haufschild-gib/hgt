# Torus convergence, conserved character energy, and damping re-entry

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Module:** `ArithmeticInnerFunctionTheory/TorusConvergenceAndBoundary.lean`

For `Uₖ=cosSum θ k`,
`Uₖ₊₁²+Uₖ²−2 cos(θ) Uₖ₊₁Uₖ=1`, hence `Uₖ₊₁²+Uₖ²≥1/2`.
Thus no character sequence tends to zero. Restricting a multidimensional character series
to one coordinate proves that every amplitude bounded away from zero produces a nonsummable
series on every nonempty torus.

Consequently, if `|f|≥c>0`, unrestricted `IsAllBaseTorusPositive f` is equivalent to
pointwise nonnegativity: nonempty tests have totalized sum zero, and the empty test reads `f`.
This is `allBaseTorusPositive_iff_nonneg_of_abs_floor`.

`boundaryOscillation_damping_not_positive` shows `1+cos(y)/2` belongs to this unrestricted
cone but multiplication by `exp(-αy)` leaves it for every `0<α≤1`.
For every `α>1`, `exists_oscillation_damping_reentry` supplies a small positive oscillation
that belongs at zero damping, fails at every rate in `(0,1]`, and re-enters at `α` with genuinely
convergent character series and without exponential convexity. The last two claims use the
existing unconditional oscillatory Bernstein dichotomy.

Final `lake --old env lean` check passed. Main `#print axioms` results:
`propext`, `Classical.choice`, `Quot.sound` only.
