# Positivity of the actual Mayer boundary response

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.
- **Input:** [actual boundary inverse](../3-formalized/gauss-mayer-actual-boundary-resolvent.md).

## Theorem

Let `b(w)=[(I−L_w)⁻¹1](0)` and `Q(s)=−∂s log b(s+1)`.
On `Re s>1`, the actual source identity is

```text
Q(s) = Σ_(n≥1) Λ(n)(1−1/n)n^(−s).
```

Its coefficients are nonnegative. They give
`3 Re Q(σ)+4 Re Q(σ+it)+Re Q(σ+2it)≥0` and an explicit
classical zero-free region of width `1/(1000 log |t|)` for `|t|≥4`.
The positivity input is this actual boundary observable; no existing
zero-free-region conclusion is used.

## Proof mechanism

The certified absolute-chamber inverse gives `b(s+1)=2ζ(s)/ζ(s+1)`.
Logarithmic differentiation and the convergent von Mangoldt series give
the displayed coefficients. Their trigonometric combination is
`2Λ(n)(1−1/n)n^(−σ)(1+cos(t log n))²≥0`.

Write `Q(s)=−ζ′/ζ(s)+ζ′/ζ(s+1)`. For `1<σ≤2`, the real-axis bound is
`Q(σ)≤1/(σ−1)+1`, since the shifted correction is nonpositive.
For `Re s≥2`, the existing absolute-series estimate
gives `|ζ′/ζ(s)|≤3`. Retaining a zero `β+iγ`, the established
archimedean and zero-resolvent bounds therefore give

```text
Re Q(σ+iγ) ≤ (log γ)/2+7/2−1/(σ−β),
Re Q(σ+2iγ) ≤ (log(2γ))/2+7/2.
```

Consequently `4/(σ−β)≤3/(σ−1)+(5/2)log γ+41/2+(log 2)/2`.
Take `σ=1+1/(100 log γ)`. For `γ≥4`, a zero with
`β>1−1/(1000 log γ)` contradicts this inequality. Conjugation handles
negative ordinates.

## Boundary of the claim

This tests source-derived transfer positivity on the actual boundary
response. It does not construct a form on all Mayer eigenfunctions,
classify the cusp sector, or give a fixed-width strip. Arbitrary positive
metrics are insufficient: existing source-functional-equation transport
admits positive metrics while retaining off-line cancellation.

## Lean certificates

`RenormalizedIntersectionTheory/GaussMayerBoundaryPositivity.lean` certifies
`shiftedBoundary_eq`, `boundarySlope_eq`, `boundarySlope_hasSum`, and
`three_four_one`.

`RenormalizedIntersectionTheory/GaussMayerBoundaryZeroFree.lean` certifies
`boundarySlope_real_le`, `boundarySlope_vertical_le`, `boundarySlope_zero_le`,
`source_dlvp`, `xiZero_re_le`, and `zeta_ne_zero`.
`positiveBoundary_order_zero` gives order zero for the actual scattering
inverse throughout the resulting part of `0<Re w<1`.

Both modules pass direct kernel checks with only `propext`,
`Classical.choice`, and `Quot.sound`.
