# Cross-load scaling capacity at scale eight

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** At `x₈=½log(8/π)`, there is `1/2<τ<1` such that
  `H(x₈)+tG(x₈)LᵀVL` is positive definite exactly when `t<τ`.
  At `t=τ` the form is positive semidefinite and singular.

Here `V=paidSevenSchur` is the fixed origin-and-scale-seven coefficient.
The native matrix `H(x₈)` is positive definite by the scale-five native theorem.

The proposed strict capacity bounds use a positive half-load and a negative
unit-load direction for the complete source. Required bounds retain the actual
unequal-pair weight, bound both sides of the compensation, and control the
omitted pairs and pure atoms. Rational surrogate signs alone do not settle
the complete-source claim.

Paper proof and Lean formalization remain open.
