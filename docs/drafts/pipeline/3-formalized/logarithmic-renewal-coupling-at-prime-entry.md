# Logarithmic renewal coupling at prime entry

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For the actual causal density `v` and renewal mass `V`, `J(ε)=∫₀^ε v(y)V(ε-y)dy` satisfies `J(ε)log(1/ε)→1` as `ε↓0`.

## Paper argument

Positivity and monotonicity give `V(ε/2)²≤J(ε)≤V(ε)²`.
The lower bound restricts the integral to `[0,ε/2]`; the upper bound uses
`V(ε-y)≤V(ε)`. The formalized normalization `V(ε)√log(1/ε)→1`
also holds after replacing `ε` by `ε/2`, because the logarithms differ by
`log 2`. Squeezing proves the stated constant exactly.

## Mathematical role

The theorem evaluates the renewal readout of the model profile `V(ε-y)`
on a strip of width `ε`. Identifying this profile, its coefficient, and
the remainder in the actual Weil resolvent at prime entry remains open.

## Lean

`CanonicalSystemOfTheWindowTower/TheLogarithmicRenewalCouplingHasItsExactNormalization.lean`:

- `monotone_logarithmicRenewalMass`
- `square_half_le_logarithmicRenewalCoupling`
- `logarithmicRenewalCoupling_le_square`
- `tendsto_logarithmicRenewalCoupling_normalized`

Plain Lean audit passes. The exact limit depends only on
`propext`, `Classical.choice`, and `Quot.sound`.
