# The golden source has an exact square-root admission threshold

- **ID:** biarithmetic-golden-source-admission
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** For `0<=a<5`, the geometric prime-five source is paid exactly when `a<sqrt(5)`. For `0<=t<=1`, the actual golden inverse-zeta source is paid exactly when `goldenPrimaryRoot*t<sqrt(5)`.

## Proof

Below the threshold the geometric tower is critical Wiener, by the checked exact
local-factor criterion, and therefore paid. At equality the corpus theorem
`criticalLine_sharpness` gives unbounded receiver energy for those same coefficients.
The explicit geometric mean `5/(5-a)` identifies the sharpness theorem's centering
with the source's actual mean.

For `sqrt(5)<=a<5`, every digit is nonnegative, so increasing the digit evaluation
parameter increases `D_a(n)` at each integer `n`. This follows directly by strong
induction from `D_a(n)=(n mod5)+a D_a(floor(n/5))`. The factor `a/(5-a)` also
increases on `[0,5)`: its difference at `a` and `s` is
`5(a-s)/[(5-a)(5-s)]`. The exact receiver identity
`A_(I_a)(n)=-a/(5-a) D_a(n)` therefore gives pointwise domination of the critical
receiver's absolute value. Its finite pronic energy is at least the critical energy,
so cannot be uniformly bounded.

The actual golden source has the same paid ideal as its primary tower, by the
checked paid-perturbation reduction. A source is paid precisely when the unit kernel
belongs to that ideal. This transfers the threshold without adding any asymptotic
profile assumption or new analytic premise.

For the usual damping `t=5^(-epsilon)`, the boundary is
`epsilon=log(phi)/log(5)`, where `phi=(1+sqrt(5))/2`. Strictly greater damping is
paid; the boundary still escapes. This logarithmic restatement needs its own Lean
normalization if exposed as a public theorem.

## Scope and verification

This is ordinary-integer floor incidence. It does not assert the same endpoint
behaviour for the intrinsic generalized-integer counting receiver, whose undamped
response is paid. The exact module, all Gram limits, and the full kernel payment
criterion are separate obligations.

- [x] Dependency-closed paper proof and exact source comparison.
- [x] Digit monotonicity, energy monotonicity, critical nonpayment, and golden threshold: scratch passed with five clean transitive audits.
- [x] Direct check of `GoldenSourceAdmission.lean`, umbrella import, and five transitive audits using only `propext`, `Classical.choice`, and `Quot.sound`.

Main declarations: `fiveDigitRow_mono`, `fiveTower_energy_mono`,
`not_receiverBounded_critical_fiveTower`, `receiverBounded_fiveTower_iff`, and
`receiverBounded_goldenArithmeticSource_iff`.
