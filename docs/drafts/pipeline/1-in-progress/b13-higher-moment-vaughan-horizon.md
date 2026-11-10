# Higher-moment filtered Vaughan horizon

- **ID:** b13-higher-moment-vaughan-horizon
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B13; independent upper bound for the centred arithmetic current.

## Proved input

For fixed `r≥1`, `0≤σ<1`, `t≥1`, `Re ε=α>0`, `|ε|≤4αt`,
`αX²=2`, `U,V≥1`, and `UV≤X`, the actual higher-moment reduction error is

`|E_r| ≪r,σ [t^(2r)(UV)^(2r)X^(1−σ−2r)+VtX^(−σ)](1+log X)`.

Its signed coefficient masses remain exact. The budgets
`(UV)^(2r)t^(2r+1)≤X^(2r+σ−1−η)` and `Vt²≤X^(σ−η)`
give `O(1/t)` error for `η>0`. Complete proof and Lean declarations:
[the centred reduction](../3-formalized/b13-higher-moment-centred-vaughan.md).

## Filtered target

For `0<σ<1`, `0<η≤min(σ/2,1/2)`, `β≥σ`, `t≥4`,
`ε=α−iξ`, `2α≤ξ≤αt`, `αX²=2`, `X≥2e UV`, and `0≤h≤1`,
the proposed degree-`d` damping-filter estimate is

`|F_h E_r| ≪r,σ,β,η,ws h^d [t^(d+2r)(UV)^(2r)X^(1−σ−2r+η)`
`                              +Vt^(d+1)X^(−σ+η)]`.

This would preserve every filter-spacing factor. The two sufficient
cutoff budgets would be

`(UV)^(2r)t^(d+2r+1)≤X^(2r+σ−1−η)`,
`Vt^(d+2)≤X^(σ−η)`.

The first-moment holomorphic half-strip argument is available, but its
higher-moment analytic and selected-mode extensions are not yet proved.
The restriction `η<σ` keeps the logarithmic error bounded along the
forward half-strip after log absorption.

## Remaining mathematical target

Higher-moment cofactor localization should leave cofactors approaching
exponent `(1−σ)/(2r)` when `V` is polynomial in height. The filtered
localization, selected-mode transfer and independent cancellation for
this actual centred arithmetic core remain open.

These reductions alone do not bound the centred current. Fixed `r` only;
no uniform growing-order estimate is proved. B13 remains unresolved.
