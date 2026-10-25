# Payment is bounded full cofactor action

- **ID:** biarithmetic-cofactor-payment-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** For a source with absolutely convergent actual mean, a critical Wiener kernel repairs the source precisely when its full finite cofactor action has uniformly bounded pronic norm.

## Exact comparison

Write `m_c=sum c(d)/d` and `A_c` for the actual centered divisor prefix.
At every integer horizon the convolution law gives

`P_(c,k)(n)=sum_(j<=n) k(j) A_c(floor(n/j)) = A_(k*c)(n)-m_c A_k(n)`.

Absolute convergence proves that the convolution mean is the product of the
actual means. The critical Wiener estimate bounds `||A_k||_T` by a constant
independent of `T`. The triangle inequality therefore proves boundedness of
`P_(c,k)` exactly when `A_(k*c)` is bounded. Taking square roots and squares
translates between the pronic norm and the corpus's receiver-payment definition.

This concerns the full kernel at every finite horizon. No finite truncation
is asserted paid, and no limiting Gram or analytic estimate is assumed.
The contribution packages the existing convolution law and critical-kernel
estimate into the precise equivalence needed for source-domain classification.

## Verification

Lean: `BiarithmeticGeometry/CofactorPaymentCriterion.lean`.
Declarations: `cofactorPrefixAction_eq_convolution_sub_mean`,
`receiverBounded_dirichletConv_iff_cofactorNorm`.

- [x] Dependency-closed paper comparison using actual means.
- [x] Direct repository source check; umbrella import wired.
- [x] Two transitive audits: only `propext`, `Classical.choice`, `Quot.sound`.
