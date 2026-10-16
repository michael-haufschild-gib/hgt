# CHMD: cross-sign bonus identity (2026-10-16)

STATUS MUST-1565. Card: 3-formalized/chmd-odd-cross-sign-bonus-2026-10-16.md. Module `RHTower/CHMDOddCrossSignBonus`
(ns RHTower.CHMDPolar, `open NonnegativeCone`), 26 decls, wired. User-requested formalization.

## Results
- `crossSignBonusL g := ∫⁻ x in Ioi 0, ofReal (jumpKernel x * ∫ u in Ioo (−x) 0, g u * g (u+x))`, `crossSignBonus := toReal`.
- `sq_sub_eq_sq_abs_sub_add` (pointwise, x > 0, f one-signed), `integral_sq_sub_eq_abs_add`,
  `measurable_integral_sq_abs_sub` / `measurable_integral_cross` (via `StronglyMeasurable.integral_prod_right'`),
  **`jumpEnergy_eq_abs_add_bonus`** (ℝ≥0∞), **`weilLevyForm_eq_abs_add_bonus`** (C²_c).
- `measurePreserving_shear` ((s,t) ↦ (s+t, −s)), `bonusPlanar`, `crossSignBonusL_eq_planar` (Tonelli),
  `lintegral_bonusPlanar_eq_quadrant`, **`crossSignBonus_eq_quadrant`** (= ∬_{s,t>0} ω(s+t) g s g t, product measure).
- Doob gauge: `levy_phiDoob_eq_abs_add_bonus`, **`levy_abs_add_bonus_le_sourceEnergy_of_odd_oneSigned`**,
  `crossSignBonus_phiDoob_eq_quadrant`.

## Lean traps
- `calc` step `_ = _ := by rw [...]` after a step closed by `rw`'s rfl: state the RHS explicitly.
- `rw [← integral_indicator]` may or may not close a goal by rfl; `congr 1` closes defeq integrands (then no funext).
- `Measure.measurePreserving_neg volume` takes the measure explicitly; `measurePreserving_prod_add volume volume`.
- `lintegral_add_left (hf : Measurable f)`, `lintegral_const_mul r hf`, `ENNReal.ofReal_ofNat`, `ENNReal.toReal_ofNat`,
  `ENNReal.mul_top (h : a ≠ 0)`; `ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall …)`.
