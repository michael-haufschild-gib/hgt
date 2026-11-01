# A positive ordinary Dirichlet twin from a rectangular lattice

- **ID:** positive-ordinary-epstein-functional-equation-twin
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ15; positivity-constrained functional-equation twins.
- **Statement:** The normalized representation series
  `D(s)=½Σ_(m,n)≠0 (m²+64n²)⁻ˢ` has nonnegative ordinary Dirichlet coefficients,
  coefficient `a(1)=1`, absolute convergence on `Re s>1`, a self-dual completion
  `F(s)=(8/π)ˢ Γ(s)D(s)` with simple poles at `0,1`, and a real zero in `(½,1)`.
  Its coefficients are not multiplicative.

## Existing inputs and missing bridges

`LatticeSectionTheory.epsteinLambda_eight_has_offLine_zero` supplies the zero.
`hasSum_epsteinLambda` supplies the lattice-indexed Dirichlet representation and
`epsteinLambda_one_sub` the paired functional equation. These do not yet state
the ordinary integer-indexed series or its scalar functional equation.

Group lattice points by `m²+64n²`; each fiber is finite. Half its cardinality is
nonnegative and its first value is one. The fibers at `5` and `13` are empty,
whereas `(1,1)` represents `65`, obstructing multiplicativity at a coprime pair.
Swapping lattice coordinates gives
`Λ_(1/8)(s)=8^(2s)Λ_8(s)`, hence `F(s)=8ˢΛ_8(s)/2` is reflection-even.

## Analytic scope

Finite order of the regularized ordinary series and a Ramanujan coefficient bound
are additional targets, not assumptions. They are required before asserting
membership in the extended Selberg class with Ramanujan bounds.
Paper proof and Lean bridges remain incomplete.
