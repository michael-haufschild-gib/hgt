# The centred Gaussian current reduces to short cofactors

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Write `F(n)=(ε/t)n^(2−σ−it)exp(−εn²)`, `ε=α−iξ`, `αX²=2`.
Let `a_U=Λ−Λ_U`, `b_V=1−ζ*μ_V`, and retain the actual cofactors

`T_UVW=Σ_n (a_U*truncAF(b_V,W))(n)F(n)`.

The centred core is `C_UVW=T_UVW+B_V L₁−(1+A_UV+D_V)P₁`, with the
same signed continuum terms as the complete Vaughan current. Set
`E_UVW=M₁−P₁−C_UVW`. Let `F_h` denote the literal polynomial damping
filter with roots `exp(hω)`, degree `d`, and Mellin twist `β`.

For `0≤σ<1`, `β≥σ`, `0<η≤1/2`, `t≥4`, `2α≤ξ≤αt`,
`U,V,W≥1`, `X≥2e UV`, and `0≤h≤1`, every integer `k≥0` gives

`|F_h E_UVW| ≤ C_E h^d t^(d+2)(UV)²X^(−1−σ+η)`
`                 + C_T h^d t^d X^(3+2k)/(UW)^(2k)`.

The constants are explicit and independent of height, scale, spacing, and
cutoffs. With `p=3+2k`, `c=σ+p+1−β`, and `A(ws)=dampingFilterCost(ws)`,

`C_E=exp(β+4)(8+2Dσ+Cσ)(1+1/η)16^d A(ws)`,
`C_T=784(k+2)! 2^p exp(2+|c|d)16^d A(ws−c)`.

Consequently the two numerical budgets

`(UV)²t^(d+3)≤X^(1+σ−η)`,
`X^(3+2k)t^(d+1)≤(UW)^(2k)`

imply `|F_h E_UVW|≤(C_E+C_T)h^d/t`. The second budget follows from
`UW≥X^(1+δ)`, `2kδ≥4`, and `t^(d+1)≤X`; this implication is also
formalized. Repeated roots and arbitrarily fast positive spacing
contraction are allowed.

For polynomial-height `V`, the product budget allows the long cutoff to
approach exponent `(1+σ)/2`. The cofactor budget then places the retained
cofactor exponent arbitrarily close above `(1−σ)/2`. The outstanding
arithmetic estimate concerns this unbalanced core.

## Proof

The product-cutoff estimate is proved in
[Power-sized Vaughan cutoffs](b13-power-sized-vaughan-cutoffs.md).

The complementary coefficient is
`a_U*(b_V−truncAF(b_V,W))`. Every nonzero summand has factors
`d>U`, `m>W`, so the coefficient vanishes for `n≤UW`. Its norm is at
most `2n²`, uniformly in all cutoffs. Since `|F(n)|≤4αn²exp(−αn²)`,
its tail is bounded by

`8α(UW)^(−2k) Σ_n n^(4+2k)exp(−αn²)`.

The elementary inequality `x^r exp(−x)≤r!` and the Gaussian lattice
bound `Σ_n exp(−(n/X)²)≤49X` give

`Σ_n n^(2r)exp(−αn²)≤49r! X^(2r+1)`.

Taking `r=k+2` and using `αX²=2` proves the independent estimate

`|tail|≤784(k+2)! X^(3+2k)/(UW)^(2k)`.

Normal convergence proves holomorphy on positive real damping. On the
logarithmic half-strip of width `1/(16t)`, the perturbed physical scale
satisfies `X exp(Re z)/2≤Y≤2X exp(Re z)`. The stronger Mellin twist
`β'=σ+p+1` reduces the resulting growth to
`exp(−Re z−t Im z)≤exp 2`.

Put `c=β'−β`. Polynomial substitution gives the exact identity

`P_h(ws)(exp(ch)Z)=exp(chd)P_h(ws−c)(Z)`.

It transfers the bounded holomorphic filter estimate back to the original
roots, losing only `exp(|c|d)` and retaining all factors `h^d`.
Absolute convergence also proves `C_UV−C_UVW=tail` exactly, so the
triangle inequality combines the two proved errors without dropping
either continuum term.

## Lean

`ExceptionalLayerTheory/GaussianVaughanCofactorTail.lean`:

- `gaussianVaughanCofactorTailCoeff_eq_zero`
- `norm_gaussianVaughanCofactorTailCoeff_le`
- `tsum_pow_mul_exp_gaussian_le`
- `norm_gaussianVaughanCofactorTail_le`
- `differentiableAt_gaussianVaughanCofactorTail`
- `gaussianCentredVaughan_sub_cofactorCurrent_eq`

`ExceptionalLayerTheory/GaussianFilteredCofactorLocalization.lean`:

- `norm_filtered_gaussianVaughanCofactorTail_le`
- `norm_filtered_gaussianCofactorReductionError_le`
- `norm_filtered_gaussianCofactorReductionError_le_inv`
- `norm_filtered_gaussianCofactorReductionError_le_inv_of_power`

Both modules pass final direct source checks without warnings. All ten
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Remaining gap

The discarded cofactors and the Vaughan reduction errors are bounded
independently of zero information. No sufficient cancellation bound for
`C_UVW` is proved. B13 remains unresolved.
