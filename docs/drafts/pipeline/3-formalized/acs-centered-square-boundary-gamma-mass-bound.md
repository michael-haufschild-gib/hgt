# Centred square boundary: arbitrarily small Gamma and one mass charge

- **ID:** acs-centered-square-boundary-gamma-mass-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every ε>0, one C≥0 satisfies, for all real t,a,b,
  `2|m(t)−m(0)||a||b| ≤ εγ(t)(a²+b²)+Cb²`, where m is the regular
  square-prime multiplier and γ is the original Gamma increment.

## Proof

The [verified high-frequency theorem](../3-formalized/acs-square-boundary-sublogarithmic-input.md)
gives |m(t)|=o(γ(t)) and γ(t)≥(log|t|)/2 eventually. Since γ tends to
infinity, subtracting the fixed m(0) preserves the little-o estimate.
Choose R≥2 so |m(t)−m(0)|≤εγ(t) for |t|≥R.

The first nonnegative term of the Gauss digamma difference, at a=1/4
and b=t/2, gives γ(t)≥16t²/(1+4t²). Consequently, on |t|≤R,
`t²≤(1+4R²)γ(t)/16`.

The regular zeta logarithmic derivative is holomorphic on the one-line,
including the removable regular part at the pole. Thus m is differentiable.
Its divided difference at zero, extended by m′(0), is continuous on the
whole real line. Compactness bounds it by B on [−R,R], so
`|m(t)−m(0)|²≤B²t²≤Kγ(t)` there, with
`K=B²(1+4R²)/16≥0`.

Set C=K/ε. On the compact interval, the product
`x=|m(t)−m(0)||a||b|` satisfies
`x²≤(εγ(t)a²)(Cb²)`. Positivity and `(A−B)²≥0` imply
`2x≤εγ(t)a²+Cb²`, which is at most the asserted bound.
Outside that interval, use `2|a||b|≤a²+b²` and the high-frequency
estimate. This proves the same inequality for every t, including zero.

## Role and remaining transfer

Integrating this inequality against the mixed Fourier density leaves only
detail mass after an arbitrarily small Gamma charge. The constant multiplier
and the ordinary mean pole cancel for original orthogonal coarse/detail
profiles. Their corrections must stay explicit during smoothing.

This card concerns the exact multiplier inequality. Its physical BV mixed
source transfer and uniform arithmetic tail cutoff are formalized on
[the parent square-mixing card](acs-square-mixed-source-lower-order.md).

## Lean verification

`ArithmeticIndexDescent/TheCenteredSquareBoundaryHasAGammaMassBound.lean`.

Declarations:

- `differentiable_squarePrimeRegularSymbol`
- `sixteen_mul_sq_div_le_gammaIncrementSymbol`
- `exists_centeredSquare_sq_le_gamma_on_compact`
- `exists_centeredSquare_abs_le_epsilon_gamma`
- `exists_centeredSquare_gamma_mass_bound`

Direct check passed, without diagnostics:

```
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheCenteredSquareBoundaryHasAGammaMassBound.lean
```

No web search, novelty checks, numerical experiments or axiom checks.
