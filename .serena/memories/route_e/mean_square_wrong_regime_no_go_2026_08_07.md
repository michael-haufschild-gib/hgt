# THIRD NO-GO: the mean-square input cannot help at short heights (2026-08-07)

Closes the successor task of `mem:route_e/halasz_route_loses_log_squared_2026_08_07` NEGATIVELY. Do not
spend further effort on the contour + mean-value shape.

## The arithmetic

`integral_norm_dirPoly_twisted_halasz` gives `V·T + M·A/V²` with `M = damped + trunc`,
`A = (T + 4L(1+log L))·S`, `S = ∑|aₙ|² = O(1)`. Optimum at `V = (2MA/T)^{1/3}`:

`∫₀^T ‖F_L‖ ≲ T^{2/3}(M·A)^{1/3}`.

Against the pointwise bound `T·M` (already available from `HalaszUniformDistance`):
- `L log L ≲ T` ⇒ `A ≍ T S` ⇒ mean-square gives `T(MS)^{1/3}`, better only when `M² > S` (weak damping);
- `L log L ≫ T` ⇒ `A ≍ L log L S` ⇒ better only when `L log L < T M²`.

Halász's application has `T` polylog and `L ≍ x`, so `L log L ≍ x log x` versus
`T M² ≍ (log x)^{A+2} e^{-2δ²}`: fails by a power of `x`. **The mean-square estimate is far worse than the
pointwise one in the regime of the application.**

Robust to sharpening: Montgomery–Vaughan's error is `(T + O(L))∑|aₙ|²`, still `O(L)`, so whenever
`T ≪ L` the level-set measure is `≲ L S/V²`, not `T S/V²`. The corpus's `4L(1+log L)` is not the problem.

## What Halász actually uses

The multiplicative factorisation of `f` — the Granville–Harper–Soundararajan recursion on `S(x)` — which
never forms a length-`x` Dirichlet polynomial and never invokes a mean-value theorem at a short height.
Different proof; that is the honest next target.

## Still valuable

`DirichletTruncationError`, `TwistedSeriesAsDirichletPoly`, `HalaszMeanSquare` are correct and reusable;
`integral_norm_dirPoly_le_of_sup_on` / `_halasz_on` are strict generalisations of the corpus's lemmas
(sup hypothesis restricted to the range). They just do not close the gap.
