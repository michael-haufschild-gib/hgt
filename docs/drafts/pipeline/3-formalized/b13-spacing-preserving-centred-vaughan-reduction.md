# Contracting filters preserve the centred Vaughan error

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Write `s=σ+it`, `ε=α−iξ`, `αX²=2`, and

`E_UV(ε)=M₁(ε)−P₁(ε)−[T_II(ε)+B_V L₁(ε)−(1+A_UV+D_V)P₁(ε)]`.

For a list `ω` of `d` fixed complex roots, set
`P_h(Z)=∏_k(Z−exp(hω_k))` and

`F_h E = Σ_j P_h.coeff(j) exp((s−β)jh) E(ε exp(−2jh))`.

If `1/2≤σ<1`, `β≥σ`, `t≥4`, `2α≤ξ≤αt`, `α>0`,
`1≤U,V≤t²`, `0≤h≤1`, and `X≥2e t⁸`, then

`|F_h E_UV| ≤ C(σ,β,ω) h^d t^(d+7)/X`.

In particular `X≥2e t^(d+8)` gives `|F_h E_UV|≤C h^d/t`.
The constant is independent of height, spacing, scale and Vaughan cutoffs.
No restriction on `ht` is needed. No hypothesis on zeros or an unproved
arithmetic estimate occurs.

An explicit constant is

`C=2 exp(β+2−σ)(8Dσ+3Cσ+8)16^d A(ω)`,

where `Dσ=gaussianSecondMomentLatticeConstant σ`,
`Cσ=gaussianLogSecondMomentConstant σ`, `A([])=1`, and

`A(ω::ws)=A(ws)[2·2^(length ws)+2|ω|(1+exp|ω|)]`.

## Proof

1. The exact infinite Vaughan decomposition and second-order lattice
   estimates give `|E_UV(ε)|≤Kσ t⁷/X`, `Kσ=8Dσ+3Cσ+8`, uniformly
   for `0<α≤ξ≤2αt`, `X≥t⁸`, and the stated cutoffs. This strengthens
   the earlier `Kσ/t` estimate.
2. All arithmetic coefficients have polynomial growth. Gaussian damping
   therefore gives local normal convergence on `Re ε>0`. Differentiation
   under the logarithmic continuum integral is dominated by its shifted
   Gaussian moment. Thus the actual `E_UV` is holomorphic there.
3. Set `f(z)=exp((s−β)z)E_UV(ε exp(−2z))`, `r=1/(16t)`.
   On `Re z>−r`, `|Im z|<r`, the rotation changes `ε` by at most
   `α/4`. Its real part lies between `3α/4` and `5α/4`; its negative
   imaginary part remains between its real part and twice that part times
   `t`. After real dilation, the physical scale `Y` satisfies
   `Y≥X exp(Re z)/2≥t⁸`. Consequently
   `|f(z)|≤2 exp(β+2−σ) Kσ t⁷/X` throughout this half-strip.
4. A bounded holomorphic function of bound `M` on a half-strip of width
   `r` has derivative bounded by `2M/r` on the half-width half-strip.
   Positive real translation preserves both domains. Integration along
   the translation segment and
   `|exp(hω)−1|≤2h|ω|(1+exp|ω|)` give
   `|f(z+h)−exp(hω)f(z)|≤hM[2/r+2|ω|(1+exp|ω|)]`.
5. Iterate through widths `r/2^k`. The result is bounded by
   `M(h/r)^d A(ω)` at zero. Polynomial evaluation at the translation
   operator identifies the iterated differences exactly with `F_h E`.
   Substitute `r=1/(16t)` and the bound from step 3.

## Scope

The reduction now retains the same `h^d` normalization as a selected-zero
signal on contracting grids. Both type-I errors and the finite head are
negligible after this normalization at the stated scales. An independent
upper bound for the centred type-II current is still missing; B13 remains
unresolved.

## Lean declarations

- `GaussianCentredVaughanCurrent.lean`:
  `norm_gaussianPrimeMoment_sub_centredVaughan_le_scale`.
- `GaussianDampingErrorAnalytic.lean`:
  `differentiableAt_gaussianCentredVaughanError`.
- `HolomorphicDampingFilters.lean`:
  `norm_dampingFilterPolynomial_sum_le`.
- `GaussianFilteredCentredVaughanError.lean`:
  `norm_filtered_gaussianCentredVaughanError_le_scale`;
  `norm_filtered_gaussianCentredVaughanError_le_inv`;
  `rotatedPrimeMomentFilter_sub_centredVaughan_eq`;
  `norm_rotatedPrimeMomentFilter_sub_centredVaughan_le_scale`.

The last two declarations identify and bound the existing literal
`rotatedPrimeMomentFilter` minus the sampled pole and centred Vaughan
terms, using exactly its geometric damping grid and sample weights.

All three new modules pass direct source checks without warnings using
`lake --old env lean GaloisForLFunctions/ExceptionalLayerTheory/<Module>.lean`.
Their nine transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.
