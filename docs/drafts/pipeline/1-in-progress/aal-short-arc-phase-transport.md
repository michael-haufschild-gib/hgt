# Short-arc phase transport

- **ID:** AAL-SAPT
- **Stage:** 1-in-progress.
- **Type:** CONJECTURE.
- **Statement:** A right zero can be transported by recurrence on an almost-closed contour together with a one-sided bound on the tail's argument change across the omitted arc.

## Target

For an isolating disc in `1/2 < Re s < 1`, seek arbitrarily high translates whose long-arc phase advance exceeds `π` and whose closing-arc phase advance exceeds `−π`. The resulting positive winding detects an enclosed zero without a density lower bound. The Euler mollifier is nonvanishing on the disc, so finite prime cuts preserve its zero divisor.

## Exact open inputs

- Quantitative recurrence on the long arc, with the omitted arc and return height controlled together.
- Control on the closing arc at those same returns: a one-sided phase bound, or reciprocal mass below the threshold proved below.
- An arithmetic property coupling the Euler product to the functional equation; contour identities alone also hold for one-off models.

## Positive result

`HTGeometry.PartialBoundaryApproximationForcesSmallValues` proves the exact alternative for analytic `f,g` with `f(c)=0`: relative error at most `η` on the long arc forces either a zero of `g` in the disc or

`−(2π−δ) log η ≤ ∫₀^δ log(1+|f|/|g|)`.

If `g` remains zero-free, some point of the gap satisfies `(exp(−(2π−δ) log η/δ)−1)|g|≤|f|`. The general theorem and its actual zeta/all-cuts specialization pass direct Lean checks with only standard axioms. The missing winding has a compulsory reciprocal-value cost, independently of zero density. [Exact theorem and proof](../3-formalized/partial-boundary-returns-force-small-values.md).

## Next conjecture

Seek long-arc returns with fixed `0<η<1`, arbitrarily large height `τ`, and omitted angle `δ≤1/log(2+|τ|)`. The corpus's `InvZetaAbscissaSubpolynomial.exists_three_circles_zeta_lower_bound_of_zeroFree_above` gives a lower bound of the form `exp(−C(log T)^α)`, `α<1`, on strict substrips of an eventual zero-free half-plane. The unresolved issue is producing returns at a compatible gap/height scale.

The disc centre `ρ`, radius `R>0`, and accuracy `η<1` are fixed before the height cutoff: for every `H`, seek `τ≥H` and `0<δ≤1/log(2+|τ|)` such that `|ζ(z+iτ)−ζ(z)|≤η|ζ(z+iτ)|` for `z=circleMap ρ R θ`, `δ≤θ≤2π`. The zero shift and a height-dependent accuracy tending to one do not meet this target.

`exists_isHeadReturn_le` bounds finite-head return height by `(7N)^N`; it does not establish the required long-arc zeta approximation. Existing head-resolution bounds control log modulus, not phase.

No quantitative return producer or AAL consequence is proved here.
