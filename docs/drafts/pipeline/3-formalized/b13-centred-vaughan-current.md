# The centred Gaussian Vaughan current

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Write `F(n)=(ε/t)n^(2−σ−it)exp(−εn²)`, `ε=α−iξ`, `αX²=2`.
Let `M=ΣΛ(n)F(n)`, `P=∫F`, `L=∫log(x)F(x)`, and
`T_UV=Σ((Λ−Λ_U)*(1−ζ*μ_V))(n)F(n)`.
With `A=Σ(Λ_U*μ_V)(b)/b`, `B=Σμ_V(b)/b`,
`D=Σμ_V(b)log(b)/b`, define `C_UV=T_UV+B L−(1+A+D)P`.

Quantitative reduction: for `1/2≤σ<1`, `t≥2`,
`0<α≤ξ≤2αt`, `1≤U,V≤t²`, `X≥t⁸`,

`|(M−P)−C_UV| ≤ (8Dσ+3Cσ+8)t⁷/X ≤ (8Dσ+3Cσ+8)/t`,

where `Dσ` and `Cσ` are the proved second-order lattice constants.
Consequently all such cutoff choices give the same centred current up to
`2(8Dσ+3Cσ+8)/t`.

## Paper proof

All series converge absolutely: type-I convolution coefficients are bounded
by `n²`, type-II coefficients by `2n²`, and Gaussian damping dominates
polynomial weights. Vaughan's identity therefore gives

`(M−P)−C_UV = H_U−(I₁−AP)+(I₂−(BL−DP))`.

The two proved second-order lattice estimates imply

`|(M−P)−C_UV| ≤ 4αU²U^(1−σ)log U`
` + 2Dσ t²X^(−1−σ)(UV)²log(UV)`
` + Cσ t²X^(−1−σ)(1+log X)V²`.

Put `q=X^(−1−σ)`. Since `σ≥1/2` and `X≥1`, `qX√X≤1`.
From `U,V≤t²` and `X≥t⁸`, `UV≤t⁴`, `√X≥t⁴`, and `t≤X`.
Furthermore `log(UV)≤4log t≤4t`, and
`1+log X=1+2log√X≤3√X`.
Multiplying the first type-I error by `X` bounds it by
`8Dσ t⁷(qXt⁴)≤8Dσ t⁷`. Multiplying the logarithmic error by `X`
bounds it by `3Cσ t⁶(qX√X)≤3Cσ t⁷`.

For the head, `U^(1−σ)≤U`, `log U≤U`, and `U⁴≤t⁸≤t⁷X`.
Its bound times `X` is at most `4αU⁴X≤4αt⁷X²=8t⁷`.
Summation proves the scale bound; `X≥t⁸` gives the inverse-height
corollary. The triangle inequality proves cutoff independence with twice
the inverse-height constant.

Dependencies: `GaussianSecondMomentTypeIPole.lean`,
`GaussianLogSecondMomentTypeIPole.lean`, and `GaussianMomentPrimeBound.lean`.

## Lean verification

Module: `ExceptionalLayerTheory/GaussianCentredVaughanCurrent.lean`.

- `tsum_gaussianMoment_vaughan`: exact complete infinite decomposition.
- `norm_gaussianPrimeMoment_sub_centredVaughan_le`: full explicit error bound.
- `norm_gaussianPrimeMoment_sub_centredVaughan_le_scale`: scale-decaying bound.
- `norm_gaussianPrimeMoment_sub_centredVaughan_le_inv`: uniform inverse-height bound.
- `norm_gaussianCentredVaughan_cutoff_sub_le`: cutoff comparison.

Direct source check passed without warnings:
`lake --old env lean GaloisForLFunctions/ExceptionalLayerTheory/GaussianCentredVaughanCurrent.lean`.
All five transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`.

## Arithmetic significance

The full pole subtraction leaves a logarithmic continuum term inside type II.
A bound on raw type II discards this cancellation. The proved estimate
removes both type-I errors and the head uniformly at sufficiently long
polynomial observation scales. It does not bound the centred type-II term
or establish B13. The spacing-preserving extension retains `h^d` in the
filtered error; see `b13-spacing-preserving-centred-vaughan-reduction.md`.
