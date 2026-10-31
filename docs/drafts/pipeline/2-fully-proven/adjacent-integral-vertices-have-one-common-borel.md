# Adjacent integral vertices have one common Borel

- **Stage:** 2-fully-proven
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** For the actual central loop extension, the adjacent coefficient-integral
  vertices `P₀,P₁` have the same intersection `B₀=P₀∩B=P₁∩B` with positive Borel.
  Both intrinsic torus coordinates have valuation one on this subgroup.

## Proof

Write `P₁=R_(X⁻¹)(P₀)` using the lifted rescaling. An element of `P₁∩B`
comes from `central(c) positive(p)` with integral coefficients and unit-valued `c`.
The Iwahori projection criterion forces `p₁₂(0)=0`. Its shifted matrix `q`
is therefore an integral Iwahori matrix. The constant determinant gives
`v(p₂₂(0))=1`. The exact splitting discrepancy is `T(X⁻¹,p₂₂)`;
tame normalization identifies this with an integer power of the unit residue,
so its valuation is one. The shifted element thus belongs to `P₀`.

Conversely, for an integral Iwahori `p`, the forward shift `R_X(p)`
is a positive integral matrix. The same determinant and tame-symbol argument
places its lifted shift in `P₀`. Applying the inverse lifted shift proves
`B₀⊆P₁`. Both inclusions yield the common intersection. The intrinsic torus
values are those already proved on `P₀∩B`.

## Lean

`HTGeometry/LoopEisenstein/IntegralAdjacentVertex.lean`:
`LoopSL2.integralAffineVertex_inf_positiveBorel`,
`LoopSL2.integralAffineVertex_borel_torus_values`. Direct check pending.
