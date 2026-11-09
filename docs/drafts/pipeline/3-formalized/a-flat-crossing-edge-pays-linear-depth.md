# A flat crossing edge pays linear depth

- **Obstacles:** B13, B112; geometry of domains supporting slow aligned returns.
- **Stage:** 3-formalized; dependency-closed paper proof and Lean audit passed.
- **Count:** Contribution 10; helpers and consequences count together.
- **Target:** Universal `c,b>0` such that, for `0<δ≤1/8`, `T≥4`,
  the maximum of `|ζ|` on
  `{s : 1/2−δ≤Re s≤4, |Im s−T|≤1}` is at least `c T^(bδ)`.
  Aligned-return bounds force a linear penetration budget
  `δ log(γ+τ)≲A log log τ+1`.
- **Distinction:** A disc presents a reflected arc of width `√δ`.
  A rectangle has a full vertical reflected edge of fixed length.
  Neither source-domain assertion is a direct specialization of the other.
- **Corpus search:** Searches for rectangle crossing growth and one-sided
  holomorphic boundary propagation found rectangle integral/argument
  machinery and the existing fixed-radius obstruction, but no linear
  shrinking-depth bound.

## Proof

Set `a=1/2+δ`, `λ=π/2`, and consider the inner rectangle
`a≤Re s≤4`, `|Im s−T|≤1`. Define
`H(s)=exp(λ(a−s+iT))−exp(λ(a−4))`.
On the left edge, `Re H≤1`. On the right edge,
`Re H=exp(λ(a−4))(cos(λ(Im s−T))−1)≤0`.
On the horizontal edges, `Re H=−exp(λ(a−4))<0`.
At `3+iT`,
`H=exp(λ(a−4))(exp λ−1)≥α`, where
`α=exp(−7π/4)(exp(π/2)−1)>0` is independent of `δ`.

Reflection bounds `|ζ|` on the inner left edge by
`C M (T/2)^(-δ)`, with universal `C≥1` and outer bound `M`.
Put `B=δ log(T/2)−log C`. For `B≥0`, the function
`ζ(s)exp(BH(s))` is bounded by `M` on the whole inner boundary.
The maximum principle and Euler anchor give `exp(αB)/2≤M`.
For `B<0`, the same logarithmic conclusion follows from `M≥1/2`.
Thus `(α/2)δ log T≤log M+log2+α log C`.

The rectangle avoids the pole since `Im s≥T−1≥3`. The weighted
function is therefore differentiable near the compact inner rectangle;
`Complex.norm_le_of_forall_mem_frontier_norm_le` applies with no
remaining analytic premise. Exponentiation gives
`c=exp(−log2−α log C)` and `b=α/2`.
Compactness supplies an actual point attaining the outer maximum.

For a source rectangle at height `γ≥0` and aligned return `τ`, apply
the bound at actual height `γ+τ`. The already-proved length estimate
`N≤1024(log τ)^6` gives
`αδ log(γ+τ)≤2[A(log1024+6log log τ)+K]`.

## Lean

Owner: `ArithmeticAuxiliaryDynamics`; module
`AFlatCrossingEdgePaysLinearDepth.lean`. Verified capstones:

- `flatCrossingWeight_pos`
- `exists_flat_crossing_logarithmic_cost`
- `exists_flat_crossing_rpow_cost`
- `exists_large_zeta_value_on_flat_crossing_box`
- `exists_aligned_flat_crossing_linear_budget`

Final audit from `formal/`:
`lake --old env lean GaloisForLFunctions/ArithmeticAuxiliaryDynamics/AFlatCrossingEdgePaysLinearDepth.lean`.
The logarithmic, actual-source large-value, and aligned-return capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Every analytic input is supplied by the zeta functional equation, Euler
anchor, and compact-domain maximum principle. Imported by
`ArithmeticAuxiliaryDynamics.lean`; no umbrella build.
No RH implication or exponent sharpness is claimed.
