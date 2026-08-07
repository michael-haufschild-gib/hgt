import Mathlib

/-!
# The half-log Cesàro average and its derivative

For a profile `F` on the half-line write

`Y(L) = ∫_0^L F`,  `P F(L) = 2L F(L) − Y(L)`,  `A(L) = Y(L) / (2√L)`.

The average `A` is normalised so that a profile `F ~ β/√L` gives `Y ~ 2β√L` and hence `A → β`, the
same limit as the half-log trace `H(L) = √L F(L)`.  Differentiating `A` produces the operator `P`
divided by a pure power:

`A'(L) = P F(L) / (4 L^{3/2})`.

So the source equation controls `A'`, an integrable quantity against `L^{-3/2}`, and convergence of
`A` follows.  This is the mechanism that produces the averaged trace.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- The primitive of a profile on the half-line. -/
noncomputable def halfLinePrimitive (F : ℝ → ℝ) (L : ℝ) : ℝ := ∫ x in (0 : ℝ)..L, F x

/-- The logarithmic Dirichlet operator `P F(L) = 2L F(L) − Y(L)`. -/
noncomputable def logDirichlet (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  2 * L * F L - halfLinePrimitive F L

/-- The half-log Cesàro average `A(L) = Y(L)/(2√L)`. -/
noncomputable def halfLogAverage (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  halfLinePrimitive F L / (2 * Real.sqrt L)

/-- The primitive differentiates to the profile. -/
theorem hasDerivAt_halfLinePrimitive {F : ℝ → ℝ} (hF : Continuous F) (L : ℝ) :
    HasDerivAt (halfLinePrimitive F) (F L) L :=
  intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
    (hF.stronglyMeasurableAtFilter _ _) hF.continuousAt

/-- **The derivative of the half-log average.**  Differentiating `Y/(2√L)` produces exactly the
logarithmic Dirichlet operator over `4L^{3/2}`. -/
theorem hasDerivAt_halfLogAverage {F : ℝ → ℝ} (hF : Continuous F) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (halfLogAverage F)
      (logDirichlet F L / (4 * L * Real.sqrt L)) L := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hY : HasDerivAt (halfLinePrimitive F) (F L) L := hasDerivAt_halfLinePrimitive hF L
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt L)) L :=
    Real.hasDerivAt_sqrt (ne_of_gt hL)
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt L))) L :=
    hs.const_mul 2
  have hne : 2 * Real.sqrt L ≠ 0 := by positivity
  have hdiv := hY.div hden hne
  have hval : (F L * (2 * Real.sqrt L) -
      halfLinePrimitive F L * (2 * (1 / (2 * Real.sqrt L)))) / (2 * Real.sqrt L) ^ 2
      = logDirichlet F L / (4 * L * Real.sqrt L) := by
    unfold logDirichlet
    have hsq2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
    field_simp
    linear_combination 4 * halfLinePrimitive F L * hsq2
  rwa [hval] at hdiv

/-- The average is the primitive against the half-log weight. -/
theorem halfLogAverage_eq {F : ℝ → ℝ} (L : ℝ) :
    halfLogAverage F L = halfLinePrimitive F L / (2 * Real.sqrt L) := rfl

/-! ## The average is a genuine average of the half-log trace

Writing `F(t) = H(t) t^{-1/2}` exhibits `Y(L)` as the pairing of `H` against the weight `t^{-1/2}`,
whose mass on `[0,L]` is exactly `2√L`.  So `A(L)` is a probability-weighted average of `H`, and
any pointwise bound on `H` passes to `A`.  This is what forces the limit of `A` to lie between the
lower and upper limits of `H`.
-/

/-- The mass of the half-log weight on `[0,L]` is `2√L`. -/
theorem integral_rpow_neg_half (L : ℝ) :
    (∫ t in (0 : ℝ)..L, t ^ (-(1 : ℝ) / 2)) = 2 * Real.sqrt L := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
  ring

/-- **A pointwise upper bound on the half-log trace passes to the average.** -/
theorem halfLogAverage_le {F : ℝ → ℝ} (hF : Continuous F) {L c : ℝ} (hL : 0 < L)
    (hH : ∀ t ∈ Set.Ioc (0 : ℝ) L, Real.sqrt t * F t ≤ c) :
    halfLogAverage F L ≤ c := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hwint : IntervalIntegrable (fun t : ℝ => c * t ^ (-(1 : ℝ) / 2)) volume 0 L := by
    refine IntervalIntegrable.const_mul ?_ c
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hL]
    norm_num
  have hmono : (∫ t in (0 : ℝ)..L, F t) ≤ ∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2) := by
    refine intervalIntegral.integral_mono_ae_restrict hL.le
      (hF.intervalIntegrable _ _) hwint ?_
    have hnull : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae hnull] with t htmem ht0
    have h0 : 0 < t := lt_of_le_of_ne htmem.1 (Ne.symm ht0)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr h0
    have hb := hH t ⟨h0, htmem.2⟩
    have hrw : t ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg h0.le]
      norm_num
    rw [hrw, mul_one_div, le_div_iff₀ hst]
    linarith [hb]
  have hval : (∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2)) = c * (2 * Real.sqrt L) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half L]
  unfold halfLogAverage halfLinePrimitive
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt L)]
  calc (∫ t in (0 : ℝ)..L, F t) ≤ ∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2) := hmono
    _ = c * (2 * Real.sqrt L) := hval


/-- **A pointwise lower bound on the half-log trace passes to the average.** -/
theorem le_halfLogAverage {F : ℝ → ℝ} (hF : Continuous F) {L c : ℝ} (hL : 0 < L)
    (hH : ∀ t ∈ Set.Ioc (0 : ℝ) L, c ≤ Real.sqrt t * F t) :
    c ≤ halfLogAverage F L := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hwint : IntervalIntegrable (fun t : ℝ => c * t ^ (-(1 : ℝ) / 2)) volume 0 L := by
    refine IntervalIntegrable.const_mul ?_ c
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hL]
    norm_num
  have hmono : (∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2)) ≤ ∫ t in (0 : ℝ)..L, F t := by
    refine intervalIntegral.integral_mono_ae_restrict hL.le hwint
      (hF.intervalIntegrable _ _) ?_
    have hnull : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae hnull] with t htmem ht0
    have h0 : 0 < t := lt_of_le_of_ne htmem.1 (Ne.symm ht0)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr h0
    have hb := hH t ⟨h0, htmem.2⟩
    have hrw : t ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg h0.le]
      norm_num
    rw [hrw, mul_one_div, div_le_iff₀ hst]
    linarith [hb]
  have hval : (∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2)) = c * (2 * Real.sqrt L) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half L]
  unfold halfLogAverage halfLinePrimitive
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt L)]
  calc c * (2 * Real.sqrt L) = ∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2) := hval.symm
    _ ≤ ∫ t in (0 : ℝ)..L, F t := hmono

end GaloisForLFunctions.HTGeometry
