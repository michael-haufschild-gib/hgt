# Effectivity on balanced complete-cell sections

- **ID:** acs-complete-cell-haar-effectivity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** acs-complete-cell-index-payment
- **Statement:** Above one fixed arithmetic index, arbitrary finite real combinations of balanced adjacent whole-cell profiles satisfy a uniform positive floor for the original full Weil form, independently of their upper support horizon.

## Actual source

For `a ≥ 1`, let `l = logCellWidth (2*a)` and `r = logCellWidth (2*a+1)`. Define
`H_a = (r/(l+r)) rawCell (2*a) - (l/(l+r)) rawCell (2*a+1)`.
Its two complete cells meet at `log (2*a+1)`, its jump there is one, and its Lean-verified square mass is `M_a = l*r/(l+r)`. All coefficients remain real and signed. No gaps are inserted between adjacent pairs.

## Inputs to prove, in order

1. Exact zero mean, orthogonality, and square mass of the actual half-line sections.
2. Exact prime compression: the translated pairing of `H_a` with `H_b` is `M_b` when `2*b+1 = m*(2*a+1)` and zero otherwise. In particular, every even multiplier vanishes. Prove this on actual cell vectors, not on a replacement matrix.
3. Derive a full-prime upper bound with diagonal coefficient strictly below `log (2*a+1)` and a horizon-independent mass error. The intended mechanism is ordinary Young allocation, the divisor identity for von Mangoldt, and summability of `Λ(m)/m^(3/2)`.
4. Derive a matching Gamma lower bound and a horizon-independent bound for the adverse pole product. Neither bound may be assumed. Mean cancellation and the completely monotone Gamma kernel are the candidate tools.
5. Combine these estimates on the original form and transfer the resulting strictly positive finite section spaces through the already formalized pole-preserving smoothing.

## Scope and integrity

This candidate supplies a concrete signed source subspace beyond separated narrow profiles. The full complete-cell index bound remains the parent target; positivity on balanced pairs alone does not establish full-source effectivity. The full Weil lower bound is not proved. Formalize each closed argument immediately, with transitive axiom audits. No stage-2 parking, sign assumptions, altered form, or discarded successor terms.

## Active Lean work

- `HaarCellPrimeCompression.lean`: exact actual-vector cancellation, orthogonality, mass bounds and contraction, finite signed-section lift, entire prime-series identity, and annihilation of even multipliers. Exact project-file audit passed; all six transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Its olean was generated solely for the bound module importing it.
- `HaarCellPrimeBound.lean`: exact project-file audit passed. `haarPrimeEnergy c X ≤ Σ a∈[1,X], (16 + log(2*a+1)/sqrt 2) * haarMass a * c a^2`, with no sign restriction or upper-horizon error. Uses `ArithmeticOrientationTheory.sum_Icc_vonMangoldt_div_mul_sqrt_le_eight` and the divisor identity; neither analytic input is assumed. All three transitive audits are clean. The two completed modules and their exact proof are recorded in [balanced complete-cell prime payment](../3-formalized/acs-balanced-complete-cell-prime-payment.md).
- `HaarCellGammaPayment.lean`: exact project-file audit passed. `haarSectionProfile_levyEnergy_ge` proves `Σ a∈[1,X], log a * M_a * c_a^2 ≤ levyEnergy (haarSectionProfile c X)` for arbitrary signed coefficients. `haarPairWidth` identifies each actual pair width as `logCellWidth a`, and the generic Gamma estimate combines with `logCellWidth a ≤ 1/a` and the exact local masses. Both transitive audits are clean.
- `HaarCellProfiles.lean`: exact project-file audit passed, including five clean transitive audits. Compact BV admission, exact mass, original prime-sum identification, and zero mean and exact square mass on every individual pair interval are formalized. These concrete identities discharge the source premises needed for Gamma and pole estimates.
- `GammaMeanZeroCoupling.lean`: exact project-file audit passed. `gamma_twoInterval_ge` pays both far-end charges of unequal mean-zero intervals by summing the existing rank-one inequality against the actual Gamma exponential series; `gamma_free_ge` pays the charge against every exterior point. Both transitive audits are clean.
- `GammaMeanZeroCapacity.lean`: exact project-file audit passed. `gamma_coherent_farCharge` sums every pair and exterior-point contribution on the whole line; its transitive audit is clean. The source may be nonzero outside the selected intervals.
- `GammaMeanZeroEnergy.lean`: exact project-file audit passed. `gammaDifference_eq_two_levyEnergy` identifies the actual symmetric kernel integral with twice the original Lévy energy for compact BV sources; `log_width_le_gammaFarCharge` proves the reciprocal-width logarithmic charge with coefficient one. Both transitive audits are clean.
- `GammaMeanZeroCoercivity.lean`: exact project-file audit passed. `levyEnergy_ge_sum_log_width` pays every local square mass by its full reciprocal-width logarithm for a finite family of disjoint mean-zero intervals, including touching intervals and arbitrary exterior source values. Its transitive audit is clean.
- The complete four-module Gamma argument is recorded in [coherent mean-zero Gamma payment](../3-formalized/acs-coherent-mean-zero-gamma-payment.md), directly in stage 3.
- `/tmp/acs-haar-pole-oscillation.lean` contains the individual positive and negative exponential-moment bounds, their finite-section lifts by weighted Cauchy–Schwarz and reciprocal telescoping, and the original pole floor `-2 * Σ M_a c_a²`. None is checked yet. The public source-support lemma in `HaarCellProfiles.lean` was exposed for this proof; its updated exact-file audit passed, with all five transitive audits clean.
- `/tmp/acs-haar-effectivity.lean` contains the intended full-form floor `Σ ((1-1/sqrt 2)*log a + 2*gammaHardyPhaseRate 0 - 20)*M_a*c_a² ≤ roughWeil (haarSectionProfile c X)` and an existential fixed lower index giving a unit-mass floor for all finite signed tails. Dependencies and the file itself must compile before either statement is counted as proved.
- `/tmp/acs-haar-smooth-effectivity.lean` contains the uniform smoothing proof, not yet checked. It uses `ArithmeticIndexDescent.realWeilForm` and finite bilinear synthesis, plus `HTGeometry.posDef_eventually_of_tendsto`; both imported oleans exist. The linear map from `Fin d` coefficients to a common pole-smoothed Haar tail is explicit. Polarizing the scalar Weil and square-mass limits gives entrywise convergence for the original form minus half the square-mass form. Finite positive-definiteness then gives one scale and a half-mass floor for the entire span, with limiting positivity supplied by the concrete tail floor. Targets are `exists_smooth_haar_positive_spaces` and `exists_smooth_haar_effectivity`: independent smooth spaces of every finite dimension, with Riemann–Roch, ampleness, and Hodge index for their source-defined L² cones. Neither theorem is counted as proved before its exact audit.
- Pole candidate: mean cancellation and exact L¹ mass `2*M_a` bound each exponential moment by `2*M_a/sqrt(2*a)`. The checked upper bound on `M_a` then yields a squared moment at most `M_a/(a*(a+1))`; these normalized weights telescope to at most one. The resulting two section moments each have square at most `Σ M_a*c_a²`, paying the adverse pole product by twice that mass. These statements are written in Lean but unverified.

## Log

- 2026-10-28 — Opened after exact smooth complete-cell realization. Testing the arithmetic cancellation on whole adjacent pairs.
