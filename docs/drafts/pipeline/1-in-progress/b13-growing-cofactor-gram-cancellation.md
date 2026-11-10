# Phase cancellation between separated growing-moment cofactors

- **ID:** b13-growing-cofactor-gram-cancellation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE under proof.
- **Obstacle:** B13 / cancellation in the centred cofactor current.

## Candidate

For the literal critical moment
`F_r(x)=(ε/t)^r x^(2r−1/2−it)exp(−εx²)`, `ε=α−iξ`, `α>0`,
consider the complete cofactor correlation along the long variable.
Its continuum correlation, normalized by the two diagonal norms, should
have modulus

`[1+(1+(ξ/α)²)((m²−k²)/(2mk))²]^(-r)`.

Thus if `m≥2k`, `ξ≥αt`, and `t≥4`, its modulus is at most `t^(-r)`.
At `r=⌊κt/log t⌋`, this gives an exponential gain in height. The
complete lattice correlation must be connected to this exact continuum
formula with the proved high-order Gaussian lattice remainder retained.

## Mechanism and required checks

The height phase in a product cancels in the long variable. The remaining
integral is `∫x^(4r−1)exp(−zx²)dx=Γ(2r)/(2z^(2r))`, where
`z=α(m²+k²)−iξ(m²−k²)`. Normalizing the diagonal cancels the Gamma
factor and all positive powers. The complex norm identity gives the
claimed suppression. The corpus supplies the integral and arbitrary-order
lattice remainders; the literal correlation identity and uniform constants
must be proved.

This would suppress separated-cofactor pairs, not the diagonal or nearby
pairs. It is not yet a bound for the centred current and cannot by itself
resolve B13. No sign of the nearby arithmetic correlations is assumed.

## Uniform lattice target

Write `S_r(m,k)` for the geometric mean of the two continuum diagonal
correlations. The proposed complete-lattice bound, for `1≤m,k≤W`, is

`|Σ_(d≥1)F_r(md)conj(F_r(kd))|`
`≤S_r(m,k){overlap_r(m,k)+(2048r³αt²W²)^r}`.

Assume `t≥1`, `|ε|≤4αt`, and `r≥1`. The derivative recursion at order
`2r` and exponent `4r−1` stays on the positive integer Gamma grid.
It gives `C_(2r)(4r−1)≤Γ(2r)(1024r³)^r/2`; the Bernoulli quotient is
at most one. Dividing by the diagonal scale and using
`4m²k²/(m²+k²)≤2W²` gives the displayed remainder.

At `αX²=2`, `X=exp(at)`, `W≤3t^(J+3)`, and `r≤t`, its base is at
most `36864t^(2J+11)exp(−2at)`, hence eventually at most `exp(−at)`.
For `m≥2k`, `|Im ε|≥αt`, and the floor order, the continuum overlap
is eventually at most `exp(−κt/2)`. No prime distribution or zero-location
estimate enters these pair bounds. Their transfer to a sufficient bound
for the complete centred current remains unproved.

## Absolute cancellation target

For `m,k≥1`, `m≥2k`, `t≥1`, and `|Im ε|≥αt`, the continuum
correlation is bounded by `(4r/t)^(2r)`. Indeed
`|z|≥|Im ε|mk`, `|ε|≤2|Im ε|`, and `Γ(2r)/2≤(2r)^(2r)`.
Under the physical sector the diagonal scale is at most `(4r)^(2r)`.
Consequently the absolute lattice error at polynomial cofactor cutoff
has base at most `589824t^(2J+13)exp(−2at)` when `r≤t`.

These bounds should yield, for every fixed integer `N≥0`,

`|Σ_(d≥1)F_r(md)conj(F_r(kd))|≤2/t^N`

uniformly in separated cofactors `1≤k≤m/2≤W/2`, all sufficiently large
`t`, the floor order, and physical damping with `αexp(2at)=2` and
`|Im ε|≥αt`. This is genuine cancellation in the complete pair sum;
the nearby-cofactor correlations and the long prime coefficients remain.
