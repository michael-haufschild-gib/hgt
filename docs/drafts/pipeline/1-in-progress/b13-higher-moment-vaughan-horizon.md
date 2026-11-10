# Higher Gaussian moments and the Vaughan cutoff horizon

- **ID:** b13-higher-moment-vaughan-horizon
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B13; independent upper bound for the centred arithmetic current.

## Target

For fixed integer `r≥1`, use
`F_r(x)=(ε/t)^r x^(2r−σ−it)exp(−εx²)`, where `0≤σ<1`,
`ε=α−iξ`, `αX²=2`, and `α≤ξ≤2αt`.

The proposed complete Vaughan error is

`≪r,σ t^(2r)(UV)^(2r)X^(1−σ−2r)(1+log X)`.

After degree-`d` damping filtering, the proposed cutoff budget is
`(UV)^(2r)t^(d+2r+1)≤X^(2r+σ−1−η)`. Together with Gaussian tail
localization, this would reduce the remaining cofactor exponent from
`(1−σ)/2` to `(1−σ)/(2r)`.

## Proved arithmetic input

The actual first type-I convolution has error

`≤K_r,σ (UV)^(2r)t^(2r)X^(1−σ−2r)log(UV)`.

Its signed reciprocal Mangoldt–Möbius mass is preserved. The complete
Gaussian divisor lattice has error `K_r,σ b^(2r−1)t^(2r)X^(1−σ−2r)`;
all lower endpoint derivatives vanish, while the last derivative is
integrable at zero. Explicit constants and Lean declarations are in
`b13-all-order-gaussian-typeI-error.md`.

## Remaining dependencies

- Higher-moment finite-head, logarithmic and selected-mode estimates.
- Actual higher-moment centred decomposition, holomorphy and spacing-preserving filter.
- Higher-moment cofactor-tail localization with its constants.
- Independent cancellation for the resulting centred arithmetic core.

For unbalanced localization, `V` may remain polynomial in height.
A weaker higher-moment logarithmic estimate can therefore suffice, such
as `O_r,σ(V²t²X^(−1−σ)(1+log X))`. For `σ>0`, even
`O_r,σ(VtX^(−σ)(1+log X))` is adequate at sufficiently large polynomial
height scales. The latter scaling follows formally from the first
variation expression; its actual infinite arithmetic estimate is unproved.

The existing `norm_sum_gaussianLogMellinWeight_sub_integral_le` holds for
every `Re w>1`; its published infinite version restricts `Re w≤2` through
sample summability. Extending Gaussian-logarithmic sample convergence to
arbitrary exponents is one direct route. Alternatively,
`∂w G_w−log(b)G_w=log(x/b)G_w`; parameter holomorphy and Cauchy on a disc
of radius `δ<1−σ` would give a logarithmic bound with an `X^δ` loss.
Neither bridge is assumed.

Fixed `r` only. No uniform growing-order estimate or centred-current
cancellation is asserted. B13 remains open.
