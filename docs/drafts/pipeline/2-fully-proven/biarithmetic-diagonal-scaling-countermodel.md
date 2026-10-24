# Diagonal scaling, mixed covariance, and stationary repair

- **ID:** biarithmetic-diagonal-scaling-countermodel
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md), A3 quantifier audit.
- **Statement:** A cyclic rank-three representation satisfies all coarse cofactor Gram constraints and exact inverse-square diagonal scaling, but fails mixed homogeneity and the corresponding stronger packet contraction. An explicit positive averaged metric restores full homogeneity without changing any diagonal.

## Paper proof

On `R³` use `B(x,y)=x·y+(x₀y₁+x₁y₀)/3`. Completing squares gives
`(2/3)|x|²≤B(x,x)≤(4/3)|x|²`. Let `P(x₀,x₁,x₂)=(x₂,x₀,x₁)` and let `v₂(j)` denote
the 2-adic valuation. Define

`V_p=p⁻¹ P^(v₂(p))`, `δ_j=j⁻¹ P^(v₂(j))e₀`, `K(j,k)=B(δ_j,δ_k)`.

Additivity of the valuation gives `V_p V_q=V_(pq)` and `V_p δ_j=δ_(pj)`.
The vectors at indices 1, 2 and 4 span `R³`, proving cyclicity. Every `P`-orbit vector of
`e₀` is a coordinate vector, so `K(j,j)=j⁻²` and `|K(j,k)|≤1/(jk)`. The metric bounds
give `B(P^r x,P^r x)≤2B(x,x)`. For `p≥2`, `2/p²≤1/p`; for `p=1` the action is the
identity. Consequently all finite packets satisfy the usual critical dilation contraction
and positivity, together with the standard `1/sqrt(jk)` radius bound.

But `K(1,2)=1/6` and `K(2,4)=0`, so mixed inverse-square homogeneity fails. Moreover
`B(V₂(e₀+e₂),V₂(e₀+e₂))=2/3>1/2=(1/4)B(e₀+e₂,e₀+e₂)`.
Thus diagonal scaling does not even give the stronger contraction on general packets.

The positive repair is `Bbar(x,y)=(B(x,y)+B(Px,Py)+B(P²x,P²y))/3`. Since `P³=1`, this
form is `P`-invariant. It obeys the same positive lower and upper metric bounds. Its associated
kernel satisfies `Kbar(pj,pk)=p⁻²Kbar(j,k)`, while `Kbar(j,j)=K(j,j)` for every `j`.
This supplies an explicit stationary metric on the same cyclic representation.

## Scope, selectivity, and novelty

This refutes the implication from diagonal scaling and coarse Gram constraints to mixed
homogeneity. It does not refute A3 restricted to actual Möbius limits, and it does not assert
realization by a regularly varying scalar row. The model uses a prime valuation, so its
selectivity is multiplicative calibration, not a signed Class III estimate.
Finite averaging is classical. The contribution is the exact simultaneous calibration of the
programme's coarse constraints and the distinction between a stationary average and an
individual source tangent. No source-subsequence realization of the average is claimed.

## Verification

- [x] Dependency-closed paper proof, including cyclicity and the positive stationary repair.
- [x] Complete scratch proof checked by Lean.
- [ ] Direct leaf check.
- [ ] Main-declaration transitive axiom audit.

Module: `GaloisForLFunctions/BiarithmeticGeometry/DiagonalScalingCountermodel.lean`.
Main declarations: `cyclicDilation_mul`, `cyclicKernel_packet_nonneg`,
`cyclicKernel_packet_dilation_le`, `cyclicKernel_not_homogeneous`,
`cyclicDilation_two_not_quarter_contractive`, `cyclicVector_cyclic`,
`stationaryCyclicKernel_homogeneous`, `stationaryCyclicKernel_diagonal`.
