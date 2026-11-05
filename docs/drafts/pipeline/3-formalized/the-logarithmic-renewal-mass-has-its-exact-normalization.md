# The logarithmic renewal mass has its exact normalization

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For the actual positive causal kernel, `V(x)=∫₀ˣv` satisfies `V(x)√log(1/x)→1` as `x↓0`.

## Proof

The exact Laplace transform gives, for `s>0` and `x≥0`,

`V(x)≤exp(sx)/κ(s)`,

`V(x)≥κ(s)⁻¹-exp(-sx/2)/κ(s/2)`.

The first follows by bounding the Laplace weight on `[0,x]` below by its
endpoint value. For the second, split the Laplace integral at `x`; the
remaining tail is at most `exp(-sx/2)` times the Laplace integral at `s/2`.

Write `x=exp(-u)`. For fixed real `c,d`, the logarithmic drift
`u+c√u+d` tends to infinity and its ratio to `u` tends to one.
The proved factor normalization therefore gives
`√u/κ(exp(u+c√u+d))→1`.
Use `s=exp(u-√u)` in the upper bound and `s=exp(u+√u)` in the lower.
The upper exponential tends to one; the discarded lower tail tends to zero.
Squeezing proves the stated limit with constant exactly one.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicRenewalMassHasItsExactNormalization.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `logarithmicRenewalMass_laplace_upper`
- `logarithmicRenewalMass_laplace_lower`
- `tendsto_sqrt_div_logReferenceFactor_drift`
- `tendsto_logarithmicRenewalMass_exp_normalized`
- `tendsto_logarithmicRenewalMass_normalized`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
The [Green operator identity](the-half-line-logarithmic-green-kernel.md)
is formalized; its application to actual Weil boundary traces remains open.
