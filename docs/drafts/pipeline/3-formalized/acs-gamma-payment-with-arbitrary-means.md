# Gamma pays logarithmic local variance with arbitrary means

- **ID:** acs-gamma-payment-with-arbitrary-means
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [complete-cell mixed payment](../1-in-progress/acs-complete-cell-mixed-payment.md)
- **Statement:** For every compact BV source and every finite disjoint family of nonempty intervals of widths at most one, the original Lévy energy pays the sum of local variances times their reciprocal-width logarithms, with arbitrary interval means.

## Goal

Remove the mean-zero restriction from Gamma payment inside complete-cell sources. Pair averages remain independent variables. This theorem controls the actual Gamma kernel; it does not assume a positive Weil residual or discharge the mixed prime term.

## Exact result

For `I=(α,α')`, `J=(β,β')`, `α<α'≤β<β'`, let

`mean_I(f) = (∫_I f)/|I|`, `V_I(f) = ∫_I (f-mean_I(f))²`.

For measurable `f,g` locally in `L²`, `gamma_twoInterval_variance_ge` proves

`V_I(f) ∫_J k(y-α) + V_J(g) ∫_I k(β'-x) ≤ ∫_I ∫_J (f(x)-g(y))² k(y-x)`

in nonnegative extended integrals, where `k` is the original `archLevyDensity`.

`gamma_free_variance_ge` proves the corresponding far-end variance charge against every exterior source value. Neither result requires local means to vanish.

For a finite disjoint interval family and any measurable `L²` source, `gamma_coherent_variance_farCharge` proves

`2 Σ_i V_i(f) ∫_ℝ gammaFarCharge(a_i,b_i,y) ≤ ∫_ℝ ∫_ℝ gammaDifference(f,x,y)`.

The source may have arbitrary values on the intervals' complement.

For compact BV `f` and widths `w_i≤1`, `levyEnergy_ge_sum_log_variance` proves the real inequality

`Σ_i log(1/w_i) * V_i(f) ≤ levyEnergy f`.

No local mean-zero or exterior vanishing condition appears.

For independent signed coefficients `u_a,v_a` on complete cells `2a,2a+1`, the concrete theorem `cellPairSum_levyEnergy_ge` gives

`Σ_(a=1..X) log(a)*haarMass(a)*(u_a-v_a)² ≤ levyEnergy(Σ_(a=1..X) u_a*rawCell(2a)+v_a*rawCell(2a+1))`.

`completePairProfile_eq_cells` proves the exact change from average/detail coordinates to these original coefficients. `intervalVariance_completePairProfile` identifies the local variance as `haarMass(a)*detail_a²`, independently of the average coordinate.

## Gates

- [x] Actual source means and variances are defined by their integrals.
- [x] Weighted product-kernel estimate proved, including its moment-matrix inequality.
- [x] Actual Gamma exponential series and exterior-point comparison discharged.
- [x] Coherent finite-family charges proved, without a local mean-zero premise.
- [x] Exact Gamma difference-energy identity and logarithmic width payment applied.
- [x] Actual complete-cell profiles retain both independent original coefficients, with exact local variance.
- [x] Direct promotion to stage 3 after exact Lean checks; no stage-2 parking.
- [x] Twelve transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

## Matched proof

The interval mean minimizes square distance to a constant. If a continuous weight satisfies `w≥m≥0`, then `m V_I(f) ≤ ∫_I (f-t)²w` for every constant `t`. The quadratic discriminant therefore bounds the weighted first moment by the remaining weighted square mass. Applying this on both intervals pays both variance charges under their positive product kernel. Each exponential Gamma slice has exactly this form. Nonnegative summation gives the original Gamma inequality. Against an exterior point, kernel monotonicity and the same constant-minimization identity give the single-interval charge. Summing pair charges and source-complement charges then covers each interval's exterior exactly once in each orientation.

On one complete pair, the profile is exactly `average_a + detail_a*haarProfile a`. Its local mean is `average_a` and its variance is `haarMass(a)*detail_a²`. The pair width is `log(1+1/a)≤1/a`, so reciprocal-width payment dominates `log(a)`. The exact coordinate identity gives `detail_a=u_a-v_a` without restricting either original coefficient.

## Lean evidence

- [IntervalVarianceMoments.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/IntervalVarianceMoments.lean): `intervalVariance_le_sub_const`, `weighted_variance_moments`, `productWeight_twoInterval_variance_le`, `rankOne_twoInterval_variance_le`.
- [GammaVarianceCoupling.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaVarianceCoupling.lean): `gamma_twoInterval_variance_ge`, `gamma_free_variance_ge`.
- [GammaVarianceCapacity.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaVarianceCapacity.lean): `gamma_coherent_variance_farCharge`.
- [GammaVarianceCoercivity.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaVarianceCoercivity.lean): `levyEnergy_ge_sum_log_variance`.
- [CompleteCellVariancePayment.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellVariancePayment.lean): `completePairProfile_eq_cells`, `intervalVariance_completePairProfile`, `completePairProfile_levyEnergy_ge`, `cellPairSum_levyEnergy_ge`.

All five exact files passed `lake --old env lean <module>.lean`, with no warnings. Audit logs: `/tmp/acs-interval-variance-final.log`, `/tmp/acs-gamma-variance-coupling-final.log`, `/tmp/acs-gamma-variance-capacity-final.log`, `/tmp/acs-gamma-variance-coercivity-final.log`, `/tmp/acs-complete-cell-variance-final.log`. All imports are wired into the ACS umbrella; the umbrella was not compiled.

## Remaining parent obligation

Full mixed Weil payment remains open. The proposed additional graph of differences of interval means and exterior mean-displacement charge have separate unchecked Lean candidates and are not part of this theorem.

## Log

- 2026-10-28 — Kernel and full Gamma coupling passed exact Lean and transitive axiom audits; promoted directly to stage 3.
