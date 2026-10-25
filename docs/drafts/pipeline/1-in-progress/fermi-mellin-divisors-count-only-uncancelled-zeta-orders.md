# Fermi Mellin divisors count only uncancelled zeta orders

- **ID:** fermi-mellin-divisors-count-only-uncancelled-zeta-orders
- **Stage:** 1-in-progress
- **Type:** EXISTING PAPER PROOF / LEAN COMPLETION
- **Parent:** [Visible poles and module multiplicity](q-iii-visible-poles-and-module-multiplicity.md)
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

Draft: `/tmp/qiii-fermi-divisor-order-check.lean`.
Target: `RHTower.meromorphicOrderAt_etaZetaQuotient`.
Corpus inputs were searched and inspected before mathlib. The scratch
explicitly checks the mathlib order API before proving the application.
Direct check, standard-axiom audit, canonical source check and umbrella
wiring remain pending. Intended owner:
`RHTower/TheFermiMellinDivisorSubtractsShiftedZetaOrders.lean`.
