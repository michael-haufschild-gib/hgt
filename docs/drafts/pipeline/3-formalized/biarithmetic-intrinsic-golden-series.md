# Exact intrinsic golden counting and centering

- **ID:** biarithmetic-intrinsic-golden-series
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; counting-kernel calibration)
- **Parent:** [Intrinsic golden module](../1-in-progress/biarithmetic-intrinsic-golden-module.md)
- **Statement:** The actual golden counting series has explicit exponential-affine coefficients. Centering convolution by the actual damped inverse mean cancels the counting pole exactly, with explicit values at both damping endpoints.

## Proof

Write `P(X)=1-5X+5X^2` and `Z(X)=P(X)/[(1-X)(1-5X)]`.
The cumulative counting series is `B(X)=Z(X)/(1-X)`. The polynomial identity

`16P(X)=5(1-X)^2-4(1-5X)+15(1-X)(1-5X)`

gives `16B(X)=5/(1-5X)-4/(1-X)^2+15/(1-X)`. Hence
`B_M=(5/16)5^M-M/4+11/16`, with increment `(5/4)5^M-1/4` and
`0<=B_M<=5^M`.

For `0<=t<=1`, put `D=5-5t+t^2`, `a=alpha*t`, `b=beta*t`.
The actual arithmetic mean is `m=(5-6t+t^2)/D`. Direct multiplication gives

`(1-tX)(1-5tX)-m(1-aX)(1-bX)=(t/D)(1-5X)(1-t^2X)`.

Multiplication by the geometric inverse factors therefore yields the exact
centered intrinsic receiver

`A_t(X)=(t/D)P(X)(1-t^2X)/[(1-X)^2(1-aX)(1-bX)]`.

At `t=0`, it is zero. At `t=1`, inverse-zeta cancellation gives `1/(1-X)`.
These are formal-series identities; no convergence hypothesis is used for the
series algebra. The actual source mean is supplied by its checked absolute
convergence theorem.

## Scope and verification

This is the intrinsic generalized-integer counting kernel. Ordinary integer
floor incidence has a different receiver. The identities calibrate that
distinction; the rank-one intrinsic tangent classification and its complete
payment domain remain separate obligations. Partial fractions and pole
cancellation are classical, with no independent originality claim.

Lean: `BiarithmeticGeometry/IntrinsicGoldenSeries.lean`.
Main declarations: `goldenIntrinsicCountSeries_partialFractions`,
`goldenIntrinsicCount_eq`, `goldenIntrinsicCount_bounds`,
`goldenIntrinsicReceiverSeries_factorization`,
`goldenIntrinsicReceiverSeries_zero`, `goldenIntrinsicReceiverSeries_one`.

- [x] Dependency-closed paper proof.
- [x] Direct repository source check; umbrella import wired.
- [x] Six transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
