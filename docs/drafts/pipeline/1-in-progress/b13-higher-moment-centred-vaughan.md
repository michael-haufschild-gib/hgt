# Higher-moment centred Vaughan reduction

- **ID:** b13-higher-moment-centred-vaughan
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B13; higher-moment unbalanced cutoff horizon.

## Target

For `r≥1`, `0≤σ<1`, `t≥1`, `Re ε=α>0`, `|ε|≤4αt`, `αX²=2`,
and `1≤U,V` with `UV≤X`, put `F_r(x)=(ε/t)^r x^(2r−σ−it)e^(−εx²)`.
The actual centred Vaughan current should satisfy

`|M_r−P_r−C_(r,U,V)|`
` ≪r,σ [t^(2r)(UV)^(2r)X^(1−σ−2r)+VtX^(−σ)](1+log X)`.

Here `C=T_II+B_V L_r−(1+A_UV+D_V)P_r`, with the original signed
reciprocal coefficient masses. No analytic cancellation input is assumed.

## Mechanism

The first type-I error is already formalized at order `2r`.
For the higher-moment logarithmic term, retain the existing first-variation
bound and extend positive-lattice summability to every Mellin exponent.
Normalize logarithms at scale `X` before taking absolute values. This gives
fibre error `O_r,σ(tX^(−σ)(1+|log(X/b)|))`, and hence the displayed
`VtX^(−σ)` term. The head is at most
`8^r U^(2r)X^(1−σ−2r)log U` when `U≤X`.

For polynomial-height `V` and `σ>0`, the weaker logarithmic error is
negligible at large scales. The high-order first type-I bound then controls
how far `U` can grow. Filter preservation, cofactor localization and the
independent centred-core bound remain separate requirements.

## Status

Derivation and Lean formalization in progress. The displayed full
reduction is not yet a theorem.

## Exact constants and proof

Write `p=2r`, `a=p−σ`, and `M(q)=∫₀∞u^q exp(−2u²)du`.
Let `B(q)=M(q+1)+M(q−1)+M(q)` and

`L_r,σ=8^r[M(a−1)+(p+1)B(a−1)+16B(a+1)]`.

All arguments of `M` exceed `−1` because `a>1`. For the logarithmic
weight `H_b(x)=log(x/b)x^(a−it)exp(−εx²)`,

`∫|H_b'|≤M_α(a−1)+|a−it|J_α(a−1)+2|ε|J_α(a+1)`.

The inequality `|log(x/b)|≤x/X+X/x+|log(X/b)|` and `αX²=2` give
`J_α(q)≤X^(q+1)B(q)(1+|log(X/b)|)`.
Use `|a−it|≤(p+1)t`, `2|ε|X²≤16t`, and
`|(ε/t)^r|≤8^r X^(−p)`. The resulting normalized first variation is
`≤L_r,σ tX^(−σ)(1+|log(X/b)|)`.

The finite lattice discrepancy is bounded by this variation. Its infinite
limit is justified by Gaussian majorants of arbitrary integer degree.
Splitting `log(x/b)=log x−log b` gives the two continuous poles exactly.
Finite support of `μ_≤V` and absolute Gaussian convergence justify divisor
reindexing. Summing `|μ(b)|≤1`, with `1≤b≤V≤X`, gives
`L_r,σ VtX^(−σ)(1+log X)`.

For `1≤n≤U`, use `Λ(n)≤log U`, `exp(−αn²)≤1`, and
`n^(p−σ)≤U^(p−σ)`. The head is at most
`(4α)^r U^p U^(1−σ)log U`, hence at most
`8^r U^p X^(1−σ−p)log U` when `U≤X`.

Vaughan's exact identity and absolute convergence yield
`M_r=H−I_1+I_log+T_II`. Subtracting the centred current leaves
`H−(I_1−A_UV P_r)+(I_log−(B_V L_r−D_V P_r))`.
Apply the head, first type-I and logarithmic bounds. With the previously
proved first type-I constant `K_r,σ`, the product estimate is

`|M_r−P_r−C| ≤ [(8^r+K_r,σ)t^p(UV)^p X^(1−σ−p)`
`                  +L_r,σ VtX^(−σ)](1+log X)`.

For `η>0`, `1+log X≤(1+1/η)X^η`. Thus the two explicit budgets

`(UV)^p t^(p+1)≤X^(p+σ−1−η)`,
`Vt²≤X^(σ−η)`

give error at most `(8^r+K_r,σ+L_r,σ)(1+1/η)/t`.
For `0<η<σ` and polynomial-height `V`, the first budget permits product
cutoffs approaching exponent `1−(1−σ)/(2r)` as the slack decreases.
At `σ=1/2`, this exponent is `3/4` for `r=1` and `7/8` for `r=2`.
These are unfiltered reduction bounds, not estimates for the remaining
centred current itself.
