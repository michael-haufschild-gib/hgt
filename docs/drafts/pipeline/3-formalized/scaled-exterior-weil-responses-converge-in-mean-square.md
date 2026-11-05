# Scaled exterior Weil responses converge in mean square

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** If a measurable complex response satisfies `F(d)/√log(1/d)→τ`, then `∫₀¹|F(hs)/√log(1/h)−τ|²ds→0`. Both actual exterior Gamma responses satisfy this law with coefficient minus their normalized endpoint readout.

## Proof

The normalized boundary response is bounded near zero. The exact identity
`log(1/(hs))=log(1/h)+log(1/s)` bounds the squared rescaled response by a
constant multiple of `1+log(1/s)`. This majorant is integrable on `(0,1]`.
The square-root logarithmic ratio tends pointwise to one. Dominated
convergence proves the assertion; the actual Gamma boundary limits apply.

## Lean

`CanonicalSystemOfTheWindowTower/TheExteriorWeilResponseHasItsScaledBoundaryLimit.lean`:
`logarithmic_boundary_limit_in_mean_square`,
`evalVectorRightExteriorResponse_scaled_mean_square`,
`evalVectorLeftExteriorResponse_scaled_mean_square`.

Plain Lean audit passes without warnings. All three declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. Wired into the umbrella.
The complete collar residual equation and kernel aperture derivative remain open.
