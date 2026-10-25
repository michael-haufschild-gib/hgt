# Fermi Mellin divisors count only uncancelled zeta orders

- **ID:** fermi-mellin-divisors-count-only-uncancelled-zeta-orders
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Visible poles and module multiplicity](../1-in-progress/q-iii-visible-poles-and-module-multiplicity.md)
- **Statement:** For `s != 0`, `Re(s)<1` and `s+epsilon != 1`,
  `ord_s etaZetaQuotient(epsilon) = ord_s zeta - ord_(s+epsilon) zeta`.

## Scope and proof

This exact formula was stated on the parent card. It concerns the Fermi
Mellin continuation and does not identify it with the centered receiver's
actual cofactor module. No arithmetic zero occurrence or source admission
is inferred.

The existing `etaZetaQuotient_eq` identifies the cleared continuation with
`(1-2^(1-s))*zeta(s)/(s*zeta(s+epsilon))` near the selected point.
`RHTower.one_sub_two_cpow_ne_zero` in `FermiNymanBeurlingHaarTarget` proves
the dyadic factor is nonzero when `Re(s)<1`. Both zeta factors are analytic
at the relevant points. Meromorphic order is unchanged by multiplication
with an analytic unit, subtracts under division, and commutes with
translation. These facts give the exact formula, with partial cancellation
retained and no assumed nonvanishing of either zeta value.

## Lean status

`RHTower.meromorphicOrderAt_etaZetaQuotient` is canonical in
`RHTower/TheFermiMellinDivisorSubtractsShiftedZetaOrders.lean`.
Corpus inputs were searched and inspected before mathlib; its order API
was checked in the scratch before canonical use. Scratch retry `45203`
and final canonical source-only audit `7871` passed. Both axiom reports
contain only `propext`, `Classical.choice`, `Quot.sound`.
The RHTower umbrella imports the leaf. No olean was needed.
Final output: `/tmp/qiii-fermi-divisor-order-canonical-final.log`.
