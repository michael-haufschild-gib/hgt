# Exponential tails and the averaged radial square

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6

Write `T_p(c,q)=∫_(u>q)u^p exp(−cu)du`, with `c>0`.
For `p>−1`, `q≥0`,

`T_p(c,0)=c^(−p−1)Γ(p+1)`,
`T_p(2c,q)≤exp(−cq)c^(−p−1)Γ(p+1)`.

These tails are strictly positive. For `N>0`, substitution `u=Nv` gives
`T_p(c/N,Nq)=N^(p+1)T_p(c,q)`.

For `q>0`, `α≥0`, power raising gives

`q^α T_p(2c,q)≤exp(−cq)c^(−p−α−1)Γ(p+α+1)`.

For `p>0`, `q>0`, the exact endpoint recurrence is

`p T_(p−1)(c,q)−c T_p(c,q)=−q^p exp(−cq)`.

Consequently the signed averaged first-atom profile from
[the frequency-average theorem](../3-formalized/bessel-cosh-frequency-average.md)
has the identity

`G(c,q)=∫_(u>q)u^(3/2)[(2u−3)²+12(1−c)u]exp(−2cu)du`.

In particular, `G(c,q)≥0` for every `q>0`, `0<c≤1`.

## Proof

The Gamma substitution gives the total mass. Split `exp(−2cu)` into two
factors, bound one by `exp(−cq)`, and enlarge the remaining domain to
the positive ray. For power raising, multiply the integrand inequality
`q^α u^p≤u^(p+α)` by the positive exponential.

Integrate the derivative of `u^p exp(−cu)`; its endpoint at infinity is
zero and both derivative terms are integrable. Taking `p=5/2` and rate
`2c` eliminates the signed endpoint in
`G=4T_(7/2)−6T_(3/2)−6q^(5/2)exp(−2cq)`, yielding
`4T_(7/2)−12cT_(5/2)+9T_(3/2)`. Its integrand factors as displayed.
This proves radial positivity after averaging, without deciding the
arithmetic phase sum.

## Lean

`CompletedArithmeticForms/ExponentialPowerTail.lean`:
`exponentialPowerTail_zero`, `exponentialPowerTail_split_upper`,
`exponentialPowerTail_raise_upper`, `exponentialPowerTail_recurrence`.

`CompletedArithmeticForms/FirstAtomExponentialProfile.lean`:
`exponentialPowerTail_pos`, `exponentialPowerTail_scale`,
`besselFirstAtomExponentialTail_eq_polynomial`,
`besselFirstAtomExponentialTail_nonneg`,
`besselFirstAtomExponentialTail_raise_upper`.

Both canonical modules checked. Capstone dependency audits use only
`propext`, `Classical.choice`, `Quot.sound`.
