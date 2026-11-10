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
