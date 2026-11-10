# Exact pole extraction from the first Gaussian type-I convolution

- **ID:** B13-TYPEI-POLE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B13; complete infinite Gaussian moment bound
- **Statement:** The actual convolution `ζ*(Λ_U*μ_V)` is its signed continuous pole term plus a remainder of order `UV log(UV)t X^(−σ)`.

## Statement

Let `s=σ+it`, `ε=α−iξ`, `0≤σ<1`, `t≥2`,
`0<α≤ξ≤2αt`, and `U,V≥1`. Put

`F(n)=(ε/t)n^(2−s)exp(−εn²)`,
`c=Λ_U*μ_V`, `A_UV=Σ_{1≤b≤UV}c(b)/b`,
`P₁(s,ε,t)=ε/(2t) Γ((3−s)/2) ε^(−(3−s)/2)`,
`Cσ=4Γ(1−σ/2)+16Γ(2−σ/2)`.

Then

`|Σ_{n≥1}(ζ*c)(n)F(n)−A_UV P₁(s,ε,t)|`
` ≤ Cσ UV log(UV)t α^(σ/2)`.

Here `ζ` in the convolution is the constant-one arithmetic function.
All series converge absolutely. No zero-location premise enters.
For `αX²=2`, the error is `≪σ UV log(UV)t X^(−σ)`.
The signed reciprocal mass `A_UV` is retained exactly.

## Proof

For `G(x)=x^w exp(−εx²)`, `1<Re w≤2`, its total variation is at most

`V=|w|/2 · α^(−Re(w)/2)Γ(Re(w)/2)`
`  +|ε| · α^(−(Re(w)+2)/2)Γ((Re(w)+2)/2)`.

Indeed, differentiate `G`; the two absolute derivative terms integrate
by the real Gaussian moment formula. On a lattice cell `[a,a+b]`,
integration by parts gives

`b G(a+b)−∫_a^(a+b)G = ∫_a^(a+b)(x−a)G'(x)dx`.

Summing cells and dividing by `b>0` bounds the discrepancy by `V`,
independently of the spacing. Absolute convergence permits the infinite
limit. Substitution `u=x²` and the complex-rate Gamma integral give

`∫₀∞G(x)dx=½Γ((w+1)/2)ε^(−(w+1)/2)`.

For `w=2−s`, `|w|≤2t` and `|ε|≤4αt`; multiplication by `|ε|/t`
gives the uniform fibre bound

`|Σ_{a≥1}F(ab)−P₁/b|≤Cσ t α^(σ/2)`.

The finite support of `c` permits absolute rearrangement of the actual
convolution into these fibres. Keep `Σc(b)/b` signed and apply the
fibre error only to the remainder. Finally `|c(b)|≤log b≤log(UV)`
and there are `UV` possible positive indices.

## Scope

This removes the pole-scale error from the first type-I term after its
exact main term is separated. The logarithmic type-I analogue is now
formalized in [its companion](b13-logarithmic-typeI-pole-extraction.md).
A [second-order estimate](b13-second-order-gaussian-lattice-cancellation.md)
further gains a factor `UVt/X` in this first type-I error scale.
Centred type-II cancellation remains open. No bound below the selected
exceptional-divisor signal, and no solution of B13, follows yet.

## Lean

- `GaussianTypeIContinuum.lean`: complex Gaussian integral, uniform finite
  and infinite lattice discrepancy, first-moment sector bound.
- `GaussianMomentTypeIPole.lean`: arithmetic weight identity, complete
  divisor fibres, actual truncated convolution and its signed pole term.

Both modules pass final direct `lake --old env lean` checks without
warnings. Eleven transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

Exact declarations in `GaloisForLFunctions.ExceptionalLayerTheory`:

- `integrableOn_gaussianMellinWeight`
- `norm_sum_gaussianMellinWeight_sub_integral_le`
- `integral_gaussianMellinWeight`
- `summable_gaussianMellinWeight_lattice`
- `norm_tsum_gaussianMellinWeight_sub_main_le`
- `norm_tsum_gaussianFirstMoment_sub_pole_le`
- `gaussianPrimeMomentWeight_eq_mellin`
- `summable_gaussianPrimeMomentWeight_dilate`
- `norm_tsum_gaussianPrimeMomentWeight_dilate_sub_pole_le`
- `norm_tsum_gaussianMoment_zeta_trunc_conv_sub_pole_le`
- `norm_tsum_gaussianMoment_zeta_trunc_conv_sub_pole_physical_le`

Both modules are imported by the exceptional-layer umbrella; the umbrella
was not compiled.
