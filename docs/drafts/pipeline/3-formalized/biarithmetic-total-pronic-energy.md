# Admission is finite total pronic energy

- **ID:** biarithmetic-total-pronic-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; exact domain comparison)
- **Parent:** [Payment graph norm](../2-fully-proven/biarithmetic-payment-graph-norm.md)
- **Statement:** Uniform finite-horizon pronic norm bounds are equivalent to summability of the positive-cell energy. This identifies actual receiver admission with finite total energy and gives the exact complex real/imaginary decomposition.

## Proof

For an arbitrary real row `f`, put
`e_n=f(n+1)^2/[(n+1)(n+2)]`. Reindexing gives
`sum_(n<T)e_n=||f||_T^2`. Every term is nonnegative, so uniform bounds on
the partial sums are equivalent to summability. A finite total sum gives
the explicit norm bound `sqrt(sum e_n)`; a norm bound `C` gives energy bound
`C^2`.

Apply this to the actual centered divisor prefix. Multiplication by a
nonzero scalar preserves the domain. For complex rows, the identity
`|z|^2=(Re z)^2+(Im z)^2` and positivity give summability exactly when
both real-component energies are summable.

## Scope and verification

No asymptotic or growth hypothesis on the row is needed. This is a domain
identity, not an independent admission estimate for an unpaid source.

Lean: `BiarithmeticGeometry/PronicEnergyDomain.lean`.
Main declarations: `sum_pronicCellEnergy_eq_norm_sq`,
`bounded_pronicNorm_iff_summable`,
`receiverBounded_iff_summable_pronicCellEnergy`,
`summable_complex_pronicEnergy_iff`.

- [x] Dependency-closed paper proof.
- [x] Direct repository source check; umbrella import wired.
- [x] Four transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
