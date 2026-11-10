# Second-order logarithmic Gaussian lattice cancellation

- **ID:** B13-SECOND-ORDER-LOG-LATTICE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B13; second-order Gaussian lattice cancellation
- **Statement:** Preserve both signed logarithmic continuum terms with remainder `≪σ V²t²X^(−1−σ)(1+log X)`.

## Statement

Let `F(x)=(ε/t)x^(2−s)e^(−εx²)`, `s=σ+it`, `ε=α−iξ`,
`0≤σ<1`, `t≥2`, `0<α≤ξ≤2αt`, `X>0`, `αX²=2`, and `V∈ℕ` with `V≤X`.
Put `B_V=Σ_{1≤b≤V}μ(b)/b`, `D_V=Σ_{1≤b≤V}μ(b)log b/b`,
`P₁=∫₀∞F(x)dx`, and `L₁=∫₀∞log x·F(x)dx`. Then

`|Σ_{n≥1}(log*μ_V)(n)F(n)−(B_V L₁−D_V P₁)|`
` ≪σ V²t²X^(−1−σ)(1+log X)`.

## Mechanism

For `G_w(x)=x^w e^(−εx²)` and `H_w,b(x)=log(x/b)G_w(x)`,

`H''=w(w−1)H_(w−2)+(2w−1)G_(w−2)`
`    −2ε(2w+1)H_w−4εG_w+4ε²H_(w+2)`.

The dangerous moment has real exponent `−σ`. The bound
`|log(x/X)|≤x/X+X/x` makes it nonintegrable at zero. Choose
`δ=(1−σ)/2>0` and use

`|log(x/X)|≤((x/X)^δ+(X/x)^δ)/δ`.

Both shifted moments then converge and retain the same Gaussian scale.
Two integrations by parts give fibre error
`≪σ bt²X^(−1−σ)(1+|log(X/b)|)`. Absolute finite Möbius summation
gives the stated arithmetic gain `Vt/X`.

## Explicit constant and proof

Put `M(q)=½·2^(−(q+1)/2)Γ((q+1)/2)`, `δ=(1−σ)/2`, and
`K(q)=(M(q+δ)+M(q−δ))/δ+M(q)`. The fibre constant is

`Cσ=4K(−σ)+5M(−σ)+80K(2−σ)+32M(2−σ)+256K(4−σ)`.

The fractional logarithm bound gives

`∫|H_w,b|≤X^(Re w+1)[(M(Re w+δ)+M(Re w−δ))/δ+|log(X/b)|M(Re w)]`.

For the second derivative use the same `δ` in all three logarithmic
moments. The smallest exponent after the negative shift is
`−σ−δ=−(1+σ)/2>−1`. Thus every moment converges.
The first derivative extends continuously to zero by
`x^r log x→0` for `r>0`. The trapezoidal error on a cell of length `b`
is at most `b²/8 ∫|H''|`, by two integrations by parts.

At `w=2−s`, `|w|,|w−1|≤2t`, `|2w±1|≤5t`, and
`|ε|X²≤8t`. Factoring `X^(Re w−1)` out of the five second-derivative
moments and using `|ε/t|≤4α` gives

`|Σ_{n≥1}log n·F(bn)−(L₁−log b·P₁)/b|`
` ≤ Cσ bt²X^(−1−σ)(1+|log(X/b)|)`.

The finite endpoint correction vanishes by absolute convergence of
the lattice series.
For `1≤b≤V≤X`, `|log(X/b)|≤log X`; `|μ(b)|≤1` and
`Σ_{b≤V}b≤V²` yield the stated convolution error. Signed reciprocal
Möbius masses are retained before estimating the remainder.

## Scope

This gains `Vt/X` over the first-variation error scale. The centred
type-II estimate and the full damping-filter bound remain open.

## Lean

`GaussianLogSecondVariation.lean` proves fractional logarithmic control,
the singular second-derivative estimate, and finite and infinite lattice
bounds with the explicit physical-scale constant.
`GaussianLogSecondMomentTypeIPole.lean` transfers the bound to the actual
`log*μ_V` convolution, retaining both signed reciprocal masses.

Exact declarations in `GaloisForLFunctions.ExceptionalLayerTheory`:

- `abs_log_div_le_fractional`
- `integral_norm_gaussianLogMellinWeight_le_fractional`
- `norm_sum_gaussianLogMellinWeight_sub_trapezoid_integral_le`
- `norm_tsum_gaussianLogMellinWeight_sub_integral_second_le`
- `norm_tsum_gaussianLogFirstMoment_sub_poles_second_physical_le`
- `norm_tsum_log_gaussianPrimeMomentWeight_dilate_sub_poles_second_le`
- `norm_tsum_gaussianMoment_log_trunc_moebius_sub_poles_second_le`

Both modules pass direct `lake --old env lean` checks without warnings.
Seven transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. Both modules are imported by the exceptional-layer
umbrella; the umbrella was not compiled.
