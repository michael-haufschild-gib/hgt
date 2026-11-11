# A growing full-window rung cannot hide off-line zeros

- **ID:** A105-full-window-interpretation
- **Stage:** 5-failed
- **Obstruction:** For a tempered configuration and any `r(T)→∞`, eventual
  `WindowPositiveAt Z (r(T))` is equivalent to every zero being on the critical line.
- **Lean:** `SelectiveArithmetic.onLine_iff_positive_along_unbounded_apertures`.

The onset aperture is either finite, contradicting the unbounded aperture law,
or infinite, which is exactly criticality.

**Positive survivor:** For each fixed aperture and every depth `0<δ≤1/2`, a tempered
configuration has positive form on that window, zeros of depth `δ` at unbounded
heights, and counting function differing from zeta's by `O(T)`. Superpose an off-line
lattice with the critical projection of zeta's divisor.

Paper proof and direct Lean check complete:
`SelectiveArithmetic.exists_zetaDensity_positive_window_deep_zeros`;
see `3-formalized/density-matched-positive-windows.md`.
The remaining A105 question concerns a smaller packet class on a growing rung.
