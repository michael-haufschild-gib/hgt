# Second-order Gaussian lattice cancellation

- **ID:** B13-SECOND-ORDER-LATTICE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B13; exact Gaussian type-I pole extraction
- **Statement:** The pole-subtracted first-moment fibre has error `≪σ b t² X^(−1−σ)`, gaining a factor `bt/X` over the existing `≪σ t X^(−σ)` scale.

## Bounds

Let `s=σ+it`, `ε=α−iξ`, `F(x)=(ε/t)x^(2−s)e^(−εx²)`,
`0≤σ<1`, `t≥2`, `0<α≤ξ≤2αt`, `X>0`, `αX²=2`, and `b>0`.
Put `P₁=ε/(2t)Γ((3−s)/2)ε^(−(3−s)/2)`.
Then

`|Σ_{n≥1}F(bn)−P₁/b| ≤ Cσ b t² X^(−1−σ)`.

For the actual first Vaughan type-I convolution, with
`U,V≥1`, `c=Λ_U*μ_V`, `A_UV=Σ_{b≤UV}c(b)/b`, this gives

`|Σ_n(ζ*c)(n)F(n)−A_UV P₁|`
` ≪σ (UV)² log(UV)t² X^(−1−σ)`.

## Proof

For `G_w=x^w e^(−εx²)`, `1<Re w≤2`,

`G_w''=w(w−1)G_(w−2)−2ε(2w+1)G_w+4ε²G_(w+2)`.

All three absolute Gaussian moments converge, including at zero.
On each cell `[a,a+b]`, put `K(x)=(x−a)(x−a−b)/2`.
Two integrations by parts give the trapezoidal remainder `−∫KG_w''`.
Here `|K|≤b²/8`; `G_w'` is continuous at zero, and its derivative is
integrable there, so no second derivative at zero is needed.
Summation, division by `b`, and the endpoint limits
`G_w(0)=G_w(∞)=0` yield the extra spacing factor.

For `w=2−s`, use `|w|,|w−1|≤2t`, `|2w+1|≤5t`, and
`|ε|≤4αt`. The three absolute Gaussian moments then give

`|ΣF(bn)−P₁/b| ≤ Dσ b t² α^((1+σ)/2)`,

`Dσ=Γ((1−σ)/2)+10Γ((3−σ)/2)+16Γ((5−σ)/2)`.

Since `αX²=2`, `α^((1+σ)/2)≤2X^(−1−σ)`, so `Cσ=2Dσ`.
Finally `|c(b)|≤log(UV)` and
`Σ_{1≤b≤UV}|c(b)|b≤(UV)²log(UV)`. Absolute convergence justifies
rearrangement into divisor fibres; their continuum terms sum exactly to
`A_UV P₁`. No zero-location or arithmetic-cancellation hypothesis enters.

## Relevance

The first type-I error gains a factor `UVt/X` in the independent
arithmetic estimate, retaining the exact signed reciprocal coefficient
mass. The signed continuum terms and the remaining unbalanced type-II region still
require control; this is not a bound for the full filtered prime current.

## Lean

`GaussianSecondVariation.lean` proves the finite trapezoidal estimate,
the infinite lattice bound, and its explicit sector and physical-scale forms.
`GaussianSecondMomentTypeIPole.lean` applies it to the actual arithmetic
fibres and truncated Mangoldt–Möbius convolution.

Exact declarations in `GaloisForLFunctions.ExceptionalLayerTheory`:

- `norm_sum_gaussianMellinWeight_sub_trapezoid_integral_le`
- `norm_tsum_gaussianMellinWeight_sub_main_second_le`
- `norm_tsum_gaussianFirstMoment_sub_pole_second_le`
- `norm_tsum_gaussianFirstMoment_sub_pole_second_physical_le`
- `norm_tsum_gaussianPrimeMomentWeight_dilate_sub_pole_second_physical_le`
- `norm_tsum_gaussianMoment_zeta_trunc_conv_sub_pole_second_physical_le`

Both modules pass direct `lake --old env lean` checks without warnings.
Six transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. Both modules are imported by the exceptional-layer
umbrella, which was not compiled.
