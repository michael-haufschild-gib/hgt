# Pole extraction from logarithmic Gaussian type I

- **ID:** B13-LOG-TYPEI-POLE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B13; first type-I pole extraction
- **Statement:** The actual `log*μ_V` convolution has two signed continuum terms and remainder `≪σ Vt X^(−σ)(1+log X)`.

## Statement

Let `s=σ+it`, `ε=α−iξ`, `0≤σ<1`, `t≥2`,
`0<α≤ξ≤2αt`, `αX²=2`, `X>0`, and `V≤X`. Put

`F(x)=(ε/t)x^(2−s)e^(−εx²)`,
`B_V=Σ_{1≤b≤V}μ(b)/b`, `D_V=Σ_{1≤b≤V}μ(b)log b/b`,
`P₁=∫₀∞F(x)dx`, `L₁=∫₀∞log x F(x)dx`.

Then

`|Σ_n(log*μ_V)(n)F(n) − (B_V L₁ − D_V P₁)|`
` ≤ Cσ Vt X^(−σ)(1+log X)`.

An explicit constant is obtained from

`M(q)=½·2^(−(q+1)/2)Γ((q+1)/2)`,
`K(q)=M(q+1)+M(q−1)+M(q)`,
`Cσ=8M(1−σ)+16K(1−σ)+128K(3−σ)`.

Both signed reciprocal masses remain exact. All series and integrals
converge absolutely; no zero-location input enters.

## Proof

For `G_w(x)=x^w e^(−εx²)`, set `H_b(x)=log(x/b)G_w(x)`.
At positive arguments,

`H_b'=G_(w−1)+w log(x/b)G_(w−1)−2ε log(x/b)G_(w+1)`.

The scale-sensitive elementary inequality

`|log(x/b)| ≤ x/X + X/x + |log(X/b)|`

follows by splitting `log(x/b)=log(x/X)+log(X/b)` and applying
`|log u|≤u+u⁻¹`. Thus, with `q=Re w` and
`Mα(r)=∫₀∞x^r e^(−αx²)dx`,

`∫₀∞|log(x/b)G_w(x)|dx`
` ≤ Mα(q+1)/X + X Mα(q−1) + |log(X/b)|Mα(q)`.

For `q>1`, every derivative integral converges. The kernel is continuous
at zero: write `log(x/b)x^w=(x log x)x^(w−1)−log b·x^w`.
On each lattice cell integration by parts gives

`b H_b(b(n+1))−∫_(bn)^(b(n+1))H_b = ∫_(bn)^(b(n+1))(x−bn)H_b'`.

Summing and dividing by `b` bounds the lattice discrepancy by
`∫₀∞|H_b'|`. Absolute convergence passes this estimate to the infinite sum.
At `αX²=2`, `Mα(r)=X^(r+1)M(r)`. For `w=2−s`,
`|w|≤2t`, `|ε|≤4αt`, and `|ε/t|≤4α`. Substitution in the
variation bound gives

`|Σ_{a≥1}log a F(ab) − (L₁−log b P₁)/b|`
` ≤ Cσ t X^(−σ)(1+|log(X/b)|)`.

Rearrange the actual convolution into these fibres. Absolute double
summability follows from `|μ_V(b)|b²` having finite support and
`Σ_a a³e^(−αa²)<∞`, using `log a≤a` and `|F(ab)|≤4α(ab)^(2−σ)e^(−αa²b²)`.
Finally `|μ_V(b)|≤1` and `0≤log(X/b)≤log X` for `1≤b≤V≤X`.
The signed fibre main terms sum to `B_V L₁−D_V P₁`.

## Scope

Together with first type-I pole extraction, both type-I lattice errors
have a full Gaussian-length saving. Their signed main terms must still
be combined with type II. In particular, the logarithmic continuum term
must not be discarded or treated as an already-annihilated simple pole.
Centred type-II cancellation and compatibility with the damping filter
remain open; B13 is not solved.

The [second-order refinement](b13-second-order-logarithmic-lattice-cancellation.md)
gains another factor `Vt/X` in the logarithmic remainder, with both
signed main terms unchanged.

## Lean

`GaussianLogarithmicContinuum.lean` proves the logarithmic lattice
comparison and its explicit physical-scale bound.
`GaussianLogarithmicTypeIPole.lean` transfers it to the actual infinite
`log*μ_V` convolution, retaining both signed reciprocal masses.

Both modules pass final direct `lake --old env lean` checks without
warnings. Nine transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`:

- `integrableOn_gaussianLogMellinWeight`
- `integral_norm_gaussianLogMellinWeight_le`
- `norm_sum_gaussianLogMellinWeight_sub_integral_le`
- `summable_gaussianLogMellinWeight_lattice`
- `norm_tsum_gaussianLogMellinWeight_sub_integral_le`
- `norm_tsum_gaussianLogFirstMoment_sub_poles_physical_le`
- `summable_log_gaussianPrimeMomentWeight_dilate`
- `norm_tsum_log_gaussianPrimeMomentWeight_dilate_sub_poles_le`
- `norm_tsum_gaussianMoment_log_trunc_moebius_sub_poles_le`

All declarations lie in `GaloisForLFunctions.ExceptionalLayerTheory`.
Both modules are imported by its umbrella; the umbrella was not compiled.
