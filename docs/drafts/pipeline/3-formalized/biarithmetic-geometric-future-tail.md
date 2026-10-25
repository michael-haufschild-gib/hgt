# Absolute bounds for the geometric future-tail operator

- **ID:** biarithmetic-geometric-future-tail
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phases](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** For `0<=b<1` and complex absolutely summable `g`, the future tail `B_b g(m)=sum_(s>=0)b^(s+1)g(m+s+1)` is absolutely summable, satisfies its exact backward recurrence, and has coefficient norm at most `b/(1-b)||g||_1`.

The absolute double series is an injective subfamily of the product
`||g(r)|| b^(s+1)`. Nonnegative reordering and the geometric sum give
the full operator bound. Splitting the first tail term proves
`B_b g(m)=b*g(m+1)+b*B_b g(m+1)`.

Lean: `BiarithmeticGeometry/GeometricFutureTail.lean`.
Audited declarations: `summable_geometricFutureMajorant`,
`geometricFutureTail_recurrence`, `summable_norm_geometricFutureTail`,
and `tsum_norm_geometricFutureTail_le`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/GeometricFutureTail.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

Identification with the expanding causal response and actual source
payment are separate obligations.
