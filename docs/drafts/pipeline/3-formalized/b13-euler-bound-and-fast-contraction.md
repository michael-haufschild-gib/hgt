# Arithmetic upper bound and fast contraction of the prime filter

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let `F` be any finite set of actual zero copies, `ρ₀∈ℂ`, and
`d=1+#{q∈F:ρq≠ρ₀}`. For every `c>max(1,σ)` and real `β`, there is
`C>0` such that, for all real `a,t` and `0≤h≤1`, the literal prime filter satisfies

`|A_{P_h}(t)| ≤ C h^d (1+|t|)^d exp(at(c−σ)/2)`.

Consequently, if `σ<1`, `a,κ>0`, and `dκ>a(1−σ)/2`, then
`A_{P_{exp(−κt)}}(t)→0`. Neither statement assumes an exceptional layer,
a zero-free strip, or a bound on the continued current.

## Proof

Put `s=σ+it`, `δ=c−σ>0`, `w=δ+iv`, and `y=exp(−at)`. Absolute
Euler convergence and Gaussian Mellin inversion give

`A_{P_h}(t)=(1/(2π))∫ P_h(exp(h(s+w−β))) K(y,w) L(Λ,s+w) dv`.

The integral contains the complete von Mangoldt series. Interchange with
the finite filter is justified by absolute integrability of each Gaussian
Euler integral. Geometric damping then yields polynomial evaluation exactly.

On a convex left half-plane, integrating the derivative of the exponential gives
`|exp(z)−exp(u)|≤exp(M)|z−u|` when `Re z,Re u≤M`.
Every filter factor is therefore bounded by
`h B(1+|t|)(1+|v|)`, with `B` depending only on the fixed line and roots.
The product retains `h^d` before taking norms.

The Euler factor is bounded by `ΣΛ(n)n^(−c)<∞`.
Also `|K(y,δ+iv)|=y^(−δ/2)|K(1,δ+iv)|`, and
`∫|K(1,δ+iv)|(1+|v|)^d dv<∞`. Integration proves the claimed bound.

For exponential contraction, the bound has rate `a(c−σ)/2−dκ`.
When `dκ>a(1−σ)/2`, choose `c>1` sufficiently close to `1`; this rate
is negative, and exponential decay absorbs the polynomial in height.

## Consequence and limit

The upper bound and exceptional-layer lower law both retain `h^d`.
Their limiting rate gap is `a(1−β)/2+π/4>0`; contraction does not close it.
This supplies an unconditional decay regime for the actual prime filter,
but no contradiction to an exceptional layer and no proof of B13.

## Novelty boundary and formalization

The corpus already supplies absolute Euler convergence, Gaussian inversion,
Gamma integrability, and the exceptional-layer lower law. The contribution
is their complete-filter upper estimate uniform in spacing and height,
and its unconditional fast-contraction consequence.

Source: `ExceptionalLayerTheory/EulerBoundsForDampingFilters.lean`.
Direct source audit passed without warnings. The four audited declarations are
`exists_divisorDampingFilter_euler_bound`, `primeDampingFilter_eq_euler_integral`,
`exists_primeDampingFilter_arithmetic_bound`, and
`tendsto_primeDampingFilter_zero_of_fast_contraction`.
Their transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
