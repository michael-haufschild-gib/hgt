# Actual elliptic closed places give the analytic Euler product

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** For `K=F₃(x,y)`, `y²=x³−x`, and `|u|<1/3`, the
  unordered product over actual affine closed places satisfies
  `∏ᵥ(1−u^{d(v)})⁻¹=(1−u)ζ_K(u)`. Including infinity gives the
  nonzero actual curve zeta function.

## Proof

Write `S_n={v:d(v)≤n}`; these sets are finite. The audited formal Euler
identity says that the coefficientwise limit of
`(1−X)∏_{v∈S_n}(1−X^{d(v)})` has inverse `ζ_K`.

For any finite set `S`, let
`Z_S=(1−X)⁻¹∏_{v∈S}(1−X^{d(v)})⁻¹`.
Its coefficients are real and nonnegative. If `S⊆T`, multiplication by
the remaining geometric factors increases every coefficient. Formal
inversion preserves coefficient stabilization, so `[X^n]Z_{S_N}`
equals `[X^n]ζ_K` whenever `N≥n`.

For arbitrary finite `S`, choose `M≥n` larger than every degree in `S`.
Then `S⊆S_M`, proving `0≤[X^n]Z_S≤[X^n]ζ_K`. If `S⊇S_n`, the reverse
inequality follows from `Z_{S_n}`, giving equality. Thus coefficients
stabilize along all finite subsets ordered by inclusion.

The audited rational expression `ζ_K=P(X)/((1−X)(1−3X))`, with
polynomial numerator `P`, is absolutely summable at `|u|<1/3`.
Its absolute coefficients therefore dominate
every evaluated finite product. Dominated convergence yields
`Z_S(u)→ζ_K(u)`. Each finite series evaluates to its literal Euler
product. Multiplication by `1−u` gives the asserted unordered product;
the degree-cutoff limit follows as well. The numerator has no zeros in
this disk, and both denominator factors are nonzero.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticAnalyticEulerProduct.lean`:
`tendsto_elliptic_euler_product`, `hasProd_elliptic_affine_euler_factors`,
`elliptic_euler_product_eq_zeta`, `elliptic_euler_product_limit_ne_zero`.
Direct Lean check passed. The product identity, degree-cutoff limit and
nonzero-limit capstones use exactly `propext`, `Classical.choice`,
`Quot.sound`.
