# Logarithmic renewal coupling at prime entry

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For the actual causal density `v` and renewal mass `V`, `J(ε)=∫₀^ε v(y)V(ε-y)dy` satisfies `J(ε)log(1/ε)→1` as `ε↓0`.

## Paper argument

Positivity and monotonicity give `V(ε/2)²≤J(ε)≤V(ε)²`.
The lower bound restricts the integral to `[0,ε/2]`; the upper bound uses
`V(ε-y)≤V(ε)`. The formalized normalization `V(ε)√log(1/ε)→1`
also holds after replacing `ε` by `ε/2`, because the logarithms differ by
`log 2`. Squeezing proves the stated constant exactly.

## Mathematical role

When a prime translation first connects the two aperture endpoints, its
localized forcing samples the opposite endpoint profile on a strip of width
`ε`. The renewal readout of that profile is `J(ε)`. Identifying this term,
its coefficient, and the remainder in the actual Weil resolvent remains open;
the scalar renewal asymptotic alone is not a prime-entry law.

## Lean status

The density, monotonicity of its cumulative integral, and exact renewal
normalization are available. The convolution comparison and limit are not
yet formalized.
