# Arbitrary kernels on the prime-five tower

- **ID:** biarithmetic-five-tower-kernel-lift
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** Extending arbitrary real coefficients by zero off powers of five gives a critical Wiener kernel exactly when the normalized coefficients are absolutely summable; its ordinary cofactor action is exactly the finite visible-power sum.

## Exact arithmetic interfaces

For `lift(f)(5^r)=f_r`, with zero elsewhere, the critical weight on the
`r`th coefficient is `1/(sqrt(5))^r`. The injection `r -> 5^r` and zero
off-support values therefore identify critical Wiener membership with
`sum_r |f_r|/(sqrt(5))^r < infinity`.

For every row `v` vanishing at zero and every natural `n`,

`sum_(j<=n) lift(f)(j) v(floor(n/j))
 = sum_(r<=log_5(n)) f_r v(floor(n/5^r))`.

The visible powers form a finite subset of `[1,n]`; all complementary
coefficients vanish. Natural logarithm inequalities prove both inclusions.
The zero horizon is included. Reading any tower-supported row at its powers
and lifting it recovers that row exactly.

## Verification

Lean: `BiarithmeticGeometry/FiveTowerKernelLift.lean`.
Main declarations: `fiveTowerKernelLift_pow`,
`criticalWiener_fiveTowerKernelLift_iff`, `fiveTowerKernelLift_cofactor_sum`.
The leaf also proves `fiveTowerKernelLift_read_of_support`.

- [x] Exact support and weight argument; no convergence interchange in the finite packet.
- [x] Direct repository leaf check; umbrella import wired.
- [x] Three main transitive audits: only `propext`, `Classical.choice`, `Quot.sound`.
