# Exact arithmetic payment on the prime-five tower

- **ID:** biarithmetic-prime-five-payment-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** For every real nonzero `a` with `|a|<5` and every critical Wiener kernel supported on powers of five, actual payment of the geometric source is equivalent to weighted square summability of its partial pole sums. At `a=sqrt(5)`, normalized coefficient partial sums must lie in `ell2`.

## Proof

Lift coefficients `f_r` to the kernel `k(5^r)=f_r`, zero elsewhere. Its
critical Wiener condition is exactly `sum_r |f_r|/sqrt(5)^r<infinity`.
The actual source prefix is `-a/(5-a) D_a`. Finite cofactor reindexing and
digit convolution therefore give the exact packet

`P_k(n)=-a/(5-a) W_x(n)`,
`x_l=a^l sum_(r<=l)f_r/a^r`.

The scalar is nonzero. The actual-mean cofactor comparison identifies payment
with bounded packet norm, and the signed digit-energy theorem identifies that
bound with `sum_l x_l^2/5^l<infinity`. This yields

`sum_l (a^2/5)^l (sum_(r<=l)f_r/a^r)^2<infinity`.

For `a=sqrt(5)`, put `f_r=sqrt(5)^r g_r`. The Wiener condition becomes
`g in ell1`, and payment becomes square summability of `sum_(r<=l)g_r`.
All source means and finite packets are the actual corpus quantities.
No profile limit, hull identification, or closedness of payment is assumed.

## Verification

Lean: `BiarithmeticGeometry/PrimeFivePaymentCriterion.lean`.
Main declarations: `receiverBounded_fiveTowerKernelLift_iff`,
`receiverBounded_critical_fiveTower_iff_partialSums`.

- [x] Dependency-closed paper proof, including negative real parameters.
- [x] Direct repository source check; umbrella import wired.
- [x] Five transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.

The complex golden-source comparison is separately formalized in
`GoldenPrimePayment.lean`. Ambient nonclosedness remains a separate claim
whose Lean check is pending.
