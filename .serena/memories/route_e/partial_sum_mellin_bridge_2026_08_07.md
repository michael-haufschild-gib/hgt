# The partial-sum Mellin bridge is built (2026-08-07)

`RHTower/Sieve/PartialSumMellinBridge.lean`, green, axiom-clean, umbrella-wired.

`LSeries_eq_mul_integral_sum_Icc (hf0 : f 0 = 0) (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re)` —
`L(f,s) = s ∫_{Ioi 1} (∑_{k ∈ Icc 0 ⌊t⌋₊} f k) · t^(-s-1)`.
Instances: `riemannZeta_eq_mul_integral_floor`, `inv_riemannZeta_eq_mul_integral_mertens`
(`1/ζ(s) = s ∫ M(⌊t⌋) t^{-s-1}`).

Reuse map (do not rebuild any of these):
- mathlib `tendsto_sum_mul_atTop_nhds_one_sub_integral₀` (Mathlib/NumberTheory/AbelSummation.lean) is
  improper Abel summation; the corpus's `primeZeta_eq_abel_integral` (RHTower/PrimeZetaAbelRepresentation)
  is the real-valued template for discharging its five hypotheses.
- `RHTower.differentiableAt_ofReal_cpow_neg`, `RHTower.deriv_ofReal_cpow_neg` (ZetaPartialSumStrip) are
  the cpow-in-a-real-variable lemmas; `RHTower.zetaSeriesCoeff`, `RHTower.sum_zetaCoeff` the ζ
  coefficients; `RHTower.LSeries_moebius_eq_inv_riemannZeta` (SquarefreeMoebiusNormalization) the 1/ζ
  identity. `RHTower.Mertens.*` (RHTower/MertensFirst) is a different module from Sieve/MertensFirst.
- mathlib `LSeriesSummable_of_bounded_of_one_lt_re` for summability of a bounded series.

Why it was worth building: the vertical kernel is `1/s`, decaying like `1/|t|`, whereas every earlier
Perron passage in the corpus is *smoothed* and its kernel costs the `∫‖W‖ ≍ N log N` that produced the
`(log N)²` loss of the pointwise Halász route. The bridge is exact — no truncation, no smoothing profile.

Traps: `squeeze_zero_norm` names its majorant `a`, not `g`; `← Real.rpow_one t` rewrites every `t` in the
goal (use `Real.rpow_add_one`); `Complex.norm_real` yields the *real* norm, so follow with
`Real.norm_eq_abs`.
