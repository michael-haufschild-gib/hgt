# Higher Gaussian moments and the Vaughan cutoff horizon

- **ID:** b13-higher-moment-vaughan-horizon
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B13; independent upper bound for the centred arithmetic current.

## Target

For fixed integer `r≥1`, replace the first moment by
`F_r(x)=(ε/t)^r x^(2r−σ−it) exp(−εx²)`, with `0≤σ<1`,
`ε=α−iξ`, `αX²=2`, and `α≤ξ≤2αt`.

Conjectured complete divisor-lattice error:

`|Σ_{n≥1} F_r(bn) − b⁻¹∫₀∞F_r| ≪r,σ b^(2r−1)t^(2r)X^(1−σ−2r)`.

The logarithmic version should gain the same power, with
`1+|log(X/b)|`. Actual Vaughan decomposition would then have error
`≪r,σ t^(2r)(UV)^(2r)X^(1−σ−2r)(1+log X)`.
After degree-`d` damping filtering, the proposed cutoff budget is
`(UV)^(2r)t^(d+2r+1)≤X^(2r+σ−1−η)`.
Combined with Gaussian tail localization, this would reduce the remaining
cofactor exponent from `(1−σ)/2` to `(1−σ)/(2r)`.

## Mechanism and open dependencies

The first `2r−1` derivatives vanish at zero. The `2r`th derivative has
integrable singularity `x^(−σ)`; its logarithmic counterpart has
`x^(−σ)log x`. Euler–Maclaurin boundary terms therefore disappear on the
complete lattice. Existing corpus arbitrary-order Euler–Maclaurin uses a
real derivative tower smooth at both endpoints; the singular-origin
complex Gaussian requires an integrable-final-derivative extension.

Required: actual Gaussian derivative tower and norm bounds; complete
lattice comparison; logarithmic comparison; actual Vaughan and filtered
reductions. No cancellation estimate for the remaining centred current
is asserted. Fixed `r` only; no uniform growing-order claim.

## Status

Conjecture under derivation. No new Lean theorem claimed.

A possible logarithmic bridge is differentiation in the Mellin exponent:
`∂w G_w−log(b)G_w=log(x/b)G_w`. Cauchy's estimate on a fixed disc of
radius `δ<1−σ` would transfer the non-logarithmic remainder with an
`X^δ` loss. The cutoff budget already allows a positive power margin.
This still requires actual parameter holomorphy and termwise differentiation;
no logarithmic bound has been assumed.

For unbalanced localization, `V` may remain polynomial in height. It is
therefore enough to prove a weaker logarithmic bound for the higher
moment, for example `O_r,σ(V²t²X^(−1−σ)(1+log X))`. Its second derivative
has exactly that Gaussian scaling after multiplication by `(ε/t)^r`.
Only the first type-I term needs order `2r` to permit a large `U`.
The case `V=1` reduces the logarithmic coefficient to the single full
logarithmic lattice. These higher-moment logarithmic bounds remain unproved.
