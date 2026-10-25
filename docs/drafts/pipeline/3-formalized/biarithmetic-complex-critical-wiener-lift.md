# Exact complex critical Wiener coordinates and golden payment

- **ID:** biarithmetic-complex-critical-wiener-lift
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** Complex absolutely summable coefficients lift linearly into the actual critical Wiener algebra, preserving norm and distance. Actual critical golden payment is exactly square summability of their complex partial sums.

For `g` in complex `ell1`, set `k(5^r)=sqrt(5)^r*g_r` and set all other
coefficients to zero. Then

`||k||_W=sum_r |g_r|`,

and the same identity holds for differences. The lift respects every
complex linear combination. The actual critical golden paid ideal pulls
back to

`sum_M |sum_(r<=M)g_r|^2<infinity`.

The construction assembles the checked real and imaginary lifts; the
complex criterion reuses the actual golden source comparison. No alternate
Wiener carrier or assumed payment characterization is introduced.

Lean: `BiarithmeticGeometry/ComplexCriticalWienerLift.lean`.
Audited declarations: `fiveComplexCriticalWienerLift_pow`,
`norm_fiveComplexCriticalWienerLift`, `fiveComplexCriticalWienerLift_linear`,
`norm_fiveComplexCriticalWienerLift_sub`, and
`mem_golden_critical_fiveComplexCriticalWienerLift_iff`.

- [x] Direct repository check with `lake --old env lean`.
- [x] Umbrella import wired; umbrella not compiled.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.

Closure and quotient-dimension conclusions require their separate proofs.
