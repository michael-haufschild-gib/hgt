# Quadratic cancellation in the Gaussian Vaughan term

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM

## Independent arithmetic estimate

Let `ε=α−iξ`, `α≥0`, and `s=σ+it`. Write
`a_d=(Λ(d)−Λ_{≤U}(d))d^(−σ)` and
`b_m=(δ_{m,1}−Σ_{k|m,k≤V}μ(k))m^(−σ)`.
These are the actual long and short Vaughan coefficients, including the
abscissa weight. For `A,B≥1` and `L≥B−1`, the type-II contribution obeys

`|Σ_{A≤n<B} [(Λ−Λ_{≤U})*(δ−𝟙*μ_{≤V})](n) n^(−s) exp(−εn²)|²`
`≤ (Σ_{1≤d≤L}|a_d|²) Σ_{1≤m₁,m₂≤L}|b_{m₁}b_{m₂}| K(m₁,m₂)`.

Here `𝟙` is the arithmetic zeta function and `δ` is the convolution identity. For each pair, put

- `P=max(1,⌊(A−1)/m₁⌋+1,⌊(A−1)/m₂⌋+1)`;
- `Q=min(L+1,⌊(B−1)/m₁⌋+1,⌊(B−1)/m₂⌋+1)`;
- `N=max(Q−P,0)`, `u=ξ(m₁²−m₂²)`, `λ=|u|/π`.

Then `K=exp(−α(m₁²+m₂²)P²) B(N,u)`, where

`B(N,0)=N`,
`B(N,u)=min(N,8N sqrt(λ)+12/sqrt(λ))` for `u≠0`.

The bound is uniform in height `t`, retains the product block and real
Gaussian damping, and assumes no zero location or unproved prime estimate.
It applies directly to `ε=complexGaussianDamping y φ` for every `y>0`
and `|φ|<π/2`, the damping of the literal rotated prime current.

## Proof

For `z(d,m)=exp(−α(dm)²) exp(i[ξ(dm)²−t log(dm)])`, positive integer
`d,m₁,m₂` satisfy

`z(d,m₁)conj(z(d,m₂))`
`=exp(−it(log m₁−log m₂)) exp(−α(m₁²+m₂²)d²) exp(iu d²)`.

Thus height contributes only a constant unit scalar. The normalized
quadratic phase has constant second derivative `u/π`. The corpus's
second-derivative test, with derivative ratio one, gives
`8N sqrt(λ)+12/sqrt(λ)` for `0<λ≤1`; for larger curvature the same
expression dominates the trivial bound. Conjugation handles negative
curvature. Every partial sum obeys the bound with the full interval length.
Abel summation against the decreasing nonnegative Gaussian therefore costs
only its first value. Both product constraints intersect in `[P,Q)`.
Cauchy–Schwarz and the exact finite convolution rearrangement give the
stated actual Vaughan bound.

The estimate has a proved nontrivial range: if `u≠0`, `λ≤1/1024` and
`48≤N sqrt(λ)`, then `B(N,u)≤N/2`. Thus the bound contains actual
oscillatory cancellation, while the diagonal keeps its Gaussian endpoint
factor and receives no oscillatory saving. At real damping `ξ=0`, every
pair uses the trivial branch. Rotation therefore supplies arithmetic
curvature as well as removing the selected mode's Gamma decay penalty.

## Corpus relation and remaining gap

The existing Vaughan estimates treat `log(1+r/u)`. Their quantitative
bounds do not apply to this weight. The new bridge uses the exact Gaussian
correlation, constant curvature, and the original von Mangoldt/Möbius
coefficients. Generic Cauchy–Schwarz, Abel summation and the derivative test
are inherited inputs, not new claims.

A type-II bound alone does not bound the complete prime filter. Type-I
estimates, dyadic aggregation, all contracting filter factors, and a
comparison with the exact selected-mode exponent remain open. No contradiction to an exceptional
layer or solution of B13 follows from this estimate alone.

## Lean certificate

Module: `ExceptionalLayerTheory/GaussianVaughanBilinearCancellation.lean`.

- `norm_sum_quadraticCharacter_le`
- `norm_sum_gaussian_quadratic_le`
- `gaussianPrimePhase_correlation`
- `norm_sum_gaussianPrimePhase_correlation_le`
- `norm_maskedGaussian_bilinear_sq_le`
- `gaussianPrimeWeight_eq`
- `norm_gaussianVaughan_typeII_sq_le`
- `quadraticSumBound_le_half`
- `norm_rotatedGaussianVaughan_typeII_sq_le`

Direct `lake --old env lean` source audit passes. All nine transitive
axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
Imported by `ExceptionalLayerTheory.lean`.
