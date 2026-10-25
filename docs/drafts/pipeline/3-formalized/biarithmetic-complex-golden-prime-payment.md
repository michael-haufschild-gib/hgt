# Complex prime-five payment for the actual golden source

- **ID:** biarithmetic-complex-golden-prime-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../2-fully-proven/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** Every complex critical Wiener kernel supported on powers of five repairs the actual golden source exactly when its weighted partial pole sums have finite square energy. The critical parameter and the fully paid zero endpoint are explicit.

## Proof

For `0<a<5`, split a supported complex kernel into real and imaginary
parts. Each is the exact lift of its coefficients at powers of five.
Critical Wiener membership supplies both real coefficient summability
conditions. The checked real payment criterion applies to each part.
Because `|z|^2=(Re z)^2+(Im z)^2` and both component energies are
nonnegative, the conjunction is equivalent to

`sum_l (a^2/5)^l |sum_(r<=l) k(5^r)/a^r|^2 < infinity`.

The actual golden paid ideal equals its primary tower's paid ideal.
For `0<t<=1`, substitute `a=alpha*t`; the actual root bounds give
`0<a<5`. At `tcrit=sqrt(5)/alpha`, one has `0<tcrit<1` and
`alpha*tcrit=sqrt(5)`, so the geometric energy weight becomes one.
Payment is exactly square summability of the partial sums of
`k(5^r)/sqrt(5)^r`.

At `t=0`, the actual source is the unit source and is critical Wiener.
Every Wiener kernel therefore repairs it. All source means and ideal
identities are those already constructed in `GoldenArithmeticSource`.

## Scope and verification

This classifies the full complex payment domain within the one-prime
subalgebra. It does not yet identify the full ordinary cofactor module,
its hull, or the closure of its paid ideal. Splitting complex square
energy is classical; no independent novelty claim is made.

Lean: `BiarithmeticGeometry/GoldenPrimePayment.lean`.
Main declarations: `mem_paidIdeal_fiveTower_iff`,
`mem_paidIdeal_golden_fiveTower_iff`,
`mem_paidIdeal_golden_critical_fiveTower_iff`, `mem_paidIdeal_golden_zero`.

- [x] Dependency-closed paper proof and exact source transfer.
- [x] Direct repository source check; umbrella import wired.
- [x] Five transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
