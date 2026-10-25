# Paid kernels cover visible shifted zero orders

- **ID:** paid-kernels-cover-visible-shifted-zero-orders
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Visible poles and module multiplicity](../1-in-progress/q-iii-visible-poles-and-module-multiplicity.md)

## Exact statement

Let `0 < epsilon < 1/2`, and let `k` belong to the actual critical Wiener paid
ideal of the damped Möbius receiver. At every `rho` with
`1/2+epsilon < Re(rho) < 1`, write `s0=rho-epsilon`. Then

`ord_rho(zeta) <= ord_s0(zeta) + ord_s0(K)`,

where `K` is the complex Dirichlet series of `k`. Thus

`ord_s0(K) >= visibleOrder := ord_rho(zeta) - ord_s0(zeta)`,

with truncated subtraction in the extended natural numbers. Every derivative
of `K` below this visible order vanishes. If the visible order is positive,
`halfPlanePoint(1/2,s0)` belongs to the actual paid obstruction hull and the
unconvolved damped Möbius receiver is unpaid.

No existence of a particular zero, common-zero configuration, or subcritical
escape is asserted. The result is an unconditional constraint on the
already defined paid ideal.

## Dependency-closed paper proof

For a real repairing kernel, the existing paid-receiver continuation theorem
produces `Phi`, analytic in `Re(s)>1/2`, and the cleared identity

`Z_epsilon(s) Phi(s) = (s+epsilon-1) zeta(s) K(s)
                      - m zeta(s) Z_epsilon(s)`

on `1/2<Re(s)<1`. Here `Z_epsilon(s)` is the entire residue-unit continuation
of `(s+epsilon-1)zeta(s+epsilon)` and `m` is the canonical convolution mean.
Both `zeta(s)` and `K(s)` are analytic in a neighborhood of `s0`.
Rearrangement gives

`Z_epsilon(s) (Phi(s)+m*zeta(s))
   = (s+epsilon-1) (zeta(s)*K(s))`.

Analytic orders add under products. The scalar `s+epsilon-1` is nonzero at
`s0`, and translation preserves analytic order, so the left side has order
`ord_rho(zeta) + ord_s0(Phi+m*zeta)`. The right side has order
`ord_s0(zeta)+ord_s0(K)`. Nonnegativity gives the inequality, including the
case of infinite order.

For a complex paid kernel, its real and imaginary parts are real repairing
kernels by the literal paid-ideal definition. Its Dirichlet series is
`K_re+i*K_im`. Multiplication by the nonzero scalar `i` preserves order, and
the order of a sum is at least the minimum of the summand orders. Applying
the real inequality to both parts proves the complex inequality. Truncated
subtraction gives the visible-order bound. The analytic order criterion for
iterated derivatives gives every stated jet vanishing condition.

Strict order loss forces each real part series to vanish at `s0`; hence
every complex paid-kernel evaluation vanishes there. The inspected
`bohrEval_halfPlanePoint` and `lSeries_toFn_eq` identities identify this as a
point of the actual obstruction hull. Its nonemptiness rules out payment of
the original receiver.

## Novelty and scope audit

The analytic order calculus and the paid-receiver continuation are existing
work. Existing AOT noncancellation requires `zeta(s0) != 0`; this refinement
allows partial cancellation and records every remaining jet order.

This is a necessary ideal constraint. It does not prove equality with the
corresponding jet ideal, nor place the visible points in each actual
cofactor module hull. The full module annihilator can strictly contain the
paid ideal. Joint generalized eigenspace dimensions have not been identified
with these arithmetic orders.

## Lean verification

Canonical source-only checks passed for
`ArithmeticOrientationTheory/TheOffLineZerosObstructTheMoebiusReceiver`
(`11733`) and
`ArithmeticOrientationTheory/PaidKernelsCoverVisibleTranslatedZeroOrders`
(`55727`). Required oleans passed, and the new leaf is umbrella-wired.
Transitive axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

Exact declarations:

- `complexMellinPairing_cleared_identity_of_repairs` supplies the actual
  Mellin identity and supports the refactored existing translated-zero proof.
- `zeta_order_le_translated_order_add_kernel_order_of_repairs` and
  `zeta_order_le_translated_order_add_paid_kernel_order` give the real and
  complex order bounds.
- `visibleTranslatedZetaOrder_le_paid_kernel_order` and
  `paid_kernel_jets_vanish_below_visible_order` give the residual multiplicity
  and every required interior jet.
- `mem_obstructionHull_moebius_of_strict_order_loss` and
  `not_receiverBounded_moebius_of_strict_order_loss` give partial-cancellation
  hull membership and the resulting source nonpayment.

No boundary jet or actual module spectral identification is claimed.
