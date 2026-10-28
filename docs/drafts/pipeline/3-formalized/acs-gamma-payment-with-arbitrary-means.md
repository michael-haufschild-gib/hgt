# Gamma coupling pays arbitrary interval variances

- **ID:** acs-gamma-payment-with-arbitrary-means
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [complete-cell mixed payment](../1-in-progress/acs-complete-cell-mixed-payment.md)
- **Statement:** Two ordered nonempty intervals retain both full far-end Gamma charges of their actual local variances, with arbitrary signed sources and arbitrary interval means.

## Goal

Remove the mean-zero restriction from Gamma payment inside complete-cell sources. Pair averages remain independent variables. This theorem controls the actual Gamma kernel; it does not assume a positive Weil residual or discharge the mixed prime term.

## Exact result

For `I=(α,α')`, `J=(β,β')`, `α<α'≤β<β'`, let

`mean_I(f) = (∫_I f)/|I|`, `V_I(f) = ∫_I (f-mean_I(f))²`.

For measurable `f,g` locally in `L²`, `gamma_twoInterval_variance_ge` proves

`V_I(f) ∫_J k(y-α) + V_J(g) ∫_I k(β'-x) ≤ ∫_I ∫_J (f(x)-g(y))² k(y-x)`

in nonnegative extended integrals, where `k` is the original `archLevyDensity`.

`gamma_free_variance_ge` proves the corresponding far-end variance charge against every exterior source value. Neither result requires local means to vanish.

## Gates

- [x] Actual source means and variances are defined by their integrals.
- [x] Weighted product-kernel estimate proved, including its moment-matrix inequality.
- [x] Actual Gamma exponential series and exterior-point comparison discharged.
- [x] Direct promotion to stage 3 after exact Lean checks; no stage-2 parking.
- [x] Six transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

## Matched proof

The interval mean minimizes square distance to a constant. If a continuous weight satisfies `w≥m≥0`, then `m V_I(f) ≤ ∫_I (f-t)²w` for every constant `t`. The quadratic discriminant therefore bounds the weighted first moment by the remaining weighted square mass. Applying this on both intervals pays both variance charges under their positive product kernel. Each exponential Gamma slice has exactly this form. Nonnegative summation gives the original Gamma inequality. Against an exterior point, kernel monotonicity and the same constant-minimization identity give the single-interval charge.

## Lean evidence

- [IntervalVarianceMoments.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/IntervalVarianceMoments.lean): `intervalVariance_le_sub_const`, `weighted_variance_moments`, `productWeight_twoInterval_variance_le`, `rankOne_twoInterval_variance_le`.
- [GammaVarianceCoupling.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaVarianceCoupling.lean): `gamma_twoInterval_variance_ge`, `gamma_free_variance_ge`.

Both exact files passed `lake --old env lean <module>.lean`, with no warnings. Audit logs: `/tmp/acs-interval-variance-final.log`, `/tmp/acs-gamma-variance-coupling-final.log`. Both imports are wired into the ACS umbrella; the umbrella was not compiled.

## Remaining parent obligation

Coherent finite-family summation and its complete-cell specialization are still under formalization. Full mixed Weil payment remains open. The proposed additional square of differences of interval means has a separate unchecked Lean candidate and is not part of this theorem.

## Log

- 2026-10-28 — Kernel and full Gamma coupling passed exact Lean and transitive axiom audits; promoted directly to stage 3.
