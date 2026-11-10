# Power-sized Vaughan cutoffs preserve the contracting filter

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let `E_UV=M₁−P₁−C_UV` be the actual centred Vaughan error and
`P_h(Z)=∏_{ω∈ws}(Z−exp(hω))`, `d=ws.length`. Write `F_h` for its literal
coefficient filter with Mellin twist `β≥σ`. For `0≤σ<1`, `0<η≤1/2`,
`t≥4`, `2α≤ξ≤αt`, `αX²=2`, `U,V≥1`, `X≥2e UV`, and `0≤h≤1`,

`|F_h E_UV| ≤ C h^d t^(d+2)(UV)² X^(−1−σ+η)`,

where

`C=exp(β+4)(8+2Dσ+Cσ)(1+1/η)16^d dampingFilterCost(ws)`.

Thus `(UV)²t^(d+3)≤X^(1+σ−η)` gives `|F_h E_UV|≤C h^d/t`.
No individual polynomial-height restriction remains on either cutoff.
For polynomial-height `V`, the admissible long cutoff approaches
`X^((1+σ)/2)` in exponent. Repeated filter roots are allowed.

## Proof

Put `K=UV`. Since `U,V≤K≤X`, the three previously proved arithmetic
remainders satisfy

`|E_UV|≤(8+2Dσ+Cσ)t²K²X^(−1−σ)(1+log X)`.

For the head, use `U^(1−σ)≤X^(1−σ)` and
`αX^(1−σ)=2X^(−1−σ)`; the other terms follow from
`log K≤log X` and `V²≤K²`. The inequality
`1+log X≤(1+1/η)X^η` gives the fractional-power bound.

On the logarithmic damping half-strip of width `1/(16t)`, the perturbed
physical scale satisfies `Y≥X exp(Re z)/2≥UV`. Consequently the same
product estimate applies throughout the half-strip. Put `q=−1−σ+η`.
The lower bound `log Y≥log X+Re z−1`, together with `−2≤q≤0`,
`Re z≥−1`, and `t|Im z|≤1/16`, bounds the twisted exponential by
`exp(β+4)X^q`. Holomorphy and the proved Cauchy filter estimate supply
`h^d(16t)^d dampingFilterCost(ws)`. The cutoff corollary multiplies its
budget by `X^(−1−σ+η)`.

## Lean

`ExceptionalLayerTheory/GaussianVaughanCutoffHorizon.lean`:

- `norm_gaussianCentredVaughanError_le_product`
- `norm_gaussianCentredVaughanError_le_product_power`
- `norm_filtered_gaussianCentredVaughanError_le_product`
- `norm_filtered_gaussianCentredVaughanError_product_le_inv`

Direct source check passes without warnings. All four transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining arithmetic problem

This enlarges the cutoffs in an actual infinite arithmetic reduction.
It supplies no cancellation estimate for the surviving centred type-II
current. The subsequent [cofactor localization](b13-unbalanced-cofactor-localization.md)
restricts the remaining arithmetic core. Its cancellation bound and B13
remain open.
