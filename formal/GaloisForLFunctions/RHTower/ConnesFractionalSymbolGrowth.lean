import GaloisForLFunctions.RHTower.ConnesLevyKernelScaling

/-!
# §VII (41), step 2: the truncated fractional symbol still grows like `t^α`

§VII (39)-(41) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The convolution operator (39) is cut off by a smooth `ψ` supported in `[-1,1]` and equal to `1`
near `0`.  Connes asserts that its Fourier multiplier still *"behaves like `|x_v|^α`"*.  The real
part of that multiplier is `−∫ ψ(|ε|)(1 − cos(2πxε))|ε|^{-1-α}dε`, so the assertion is the lower
bound proved here:

  `∫_0^∞ ψ(ε)(1 − cos(tε))ε^{-1-α}dε ≥ C_α t^α − 2δ^{-α}/α`,

where `δ > 0` is any radius on which `ψ = 1`.  The truncation costs only the *fixed* constant
`2δ^{-α}/α`, because where `ψ ≠ 1` we have `ε ≥ δ`, the factor `1 − cos` is bounded by `2`, and
`ε^{-1-α}` has finite mass on `[δ,∞)`.  The unbounded growth therefore survives the cut.
-/

open MeasureTheory Real Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The `t`-scaled kernel `(1 − cos(tε))ε^{-1-α}`. -/
def connesLevyKernelAt (α t ε : ℝ) : ℝ := (1 - Real.cos (t * ε)) * ε ^ (-1 - α)

theorem connesLevyKernelAt_nonneg (α t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ connesLevyKernelAt α t ε :=
  mul_nonneg (by linarith [Real.cos_le_one (t * ε)]) (Real.rpow_nonneg hε _)

theorem connesLevyKernelAt_continuousOn (α t : ℝ) :
    ContinuousOn (connesLevyKernelAt α t) (Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
  · exact continuousAt_const.sub (Real.continuous_cos.continuousAt.comp
      (continuousAt_const.mul continuousAt_id))
  · exact Real.continuousAt_rpow_const x (-1 - α) (Or.inl hx0)

theorem connes_levyAt_integrableOn_Ioc {α : ℝ} (hα : α < 2) (t : ℝ) :
    IntegrableOn (connesLevyKernelAt α t) (Ioc (0 : ℝ) 1) volume := by
  have hmaj : IntegrableOn (fun ε : ℝ => t ^ 2 * (ε ^ (1 - α) / 2)) (Ioc (0 : ℝ) 1) volume := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (1 : ℝ))
      (r := 1 - α) (by linarith)).1
    exact (h.div_const 2).const_mul _
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (connesLevyKernelAt_continuousOn α t).mono Ioc_subset_Ioi_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with ε hε
    have hε0 : (0 : ℝ) < ε := hε.1
    have hnn := connesLevyKernelAt_nonneg α t hε0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hcos : 1 - Real.cos (t * ε) ≤ t ^ 2 * ε ^ 2 / 2 := by
      have h := Real.one_sub_sq_div_two_le_cos (x := t * ε)
      have hsq : (t * ε) ^ 2 = t ^ 2 * ε ^ 2 := by ring
      rw [hsq] at h
      linarith
    have hpow : (0 : ℝ) < ε ^ (-1 - α) := Real.rpow_pos_of_pos hε0 _
    have hprod : ε ^ (2 : ℕ) * ε ^ (-1 - α) = ε ^ (1 - α) := by
      rw [← Real.rpow_natCast ε 2, ← Real.rpow_add hε0]
      congr 1
      push_cast
      ring
    calc connesLevyKernelAt α t ε
        = (1 - Real.cos (t * ε)) * ε ^ (-1 - α) := rfl
      _ ≤ (t ^ 2 * ε ^ 2 / 2) * ε ^ (-1 - α) := mul_le_mul_of_nonneg_right hcos hpow.le
      _ = t ^ 2 * (ε ^ (1 - α) / 2) := by
          rw [← hprod]; ring

theorem connes_levyAt_integrableOn_Ioi_one {α : ℝ} (hα : 0 < α) (t : ℝ) :
    IntegrableOn (connesLevyKernelAt α t) (Ioi (1 : ℝ)) volume := by
  have hmaj : IntegrableOn (fun ε : ℝ => 2 * ε ^ (-1 - α)) (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt (a := -1 - α) (by linarith) one_pos).const_mul 2
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (connesLevyKernelAt_continuousOn α t).mono (Set.Ioi_subset_Ioi (by norm_num))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ε hε
    have hε0 : (0 : ℝ) < ε := lt_trans one_pos hε
    have hnn := connesLevyKernelAt_nonneg α t hε0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hcos : 1 - Real.cos (t * ε) ≤ 2 := by
      have := Real.neg_one_le_cos (t * ε)
      linarith
    exact mul_le_mul_of_nonneg_right hcos (Real.rpow_nonneg hε0.le _)

theorem connes_levyAt_integrableOn {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (t : ℝ) :
    IntegrableOn (connesLevyKernelAt α t) (Ioi (0 : ℝ)) volume := by
  have hu := (connes_levyAt_integrableOn_Ioc hα2 t).union
    (connes_levyAt_integrableOn_Ioi_one hα0 t)
  rwa [show Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 from Ioc_union_Ioi_eq_Ioi (by norm_num)] at hu

/-- Connes' truncated symbol integral of (39). -/
def connesTruncatedLevy (α : ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ ε in Ioi (0 : ℝ), ψ ε * connesLevyKernelAt α t ε

/-- The mass discarded by the truncation is a fixed constant, uniformly in `t`. -/
theorem connes_levy_truncation_defect_le {α : ℝ} (hα0 : 0 < α)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hψδ : ∀ x ∈ Ioc (0 : ℝ) δ, ψ x = 1) (t : ℝ) :
    (∫ ε in Ioi (0 : ℝ), (1 - ψ ε) * connesLevyKernelAt α t ε) ≤ 2 * δ ^ (-α) / α := by
  set D : ℝ → ℝ := fun ε => (1 - ψ ε) * connesLevyKernelAt α t ε with hD
  have hDnn : ∀ ε : ℝ, 0 < ε → 0 ≤ D ε := fun ε hε =>
    mul_nonneg (by linarith [hψ1 ε]) (connesLevyKernelAt_nonneg α t hε.le)
  have hDzero : ∀ ε ∈ Ioc (0 : ℝ) δ, D ε = 0 := by
    intro ε hε
    simp only [hD, hψδ ε hε, sub_self, zero_mul]
  have hDmeas : AEStronglyMeasurable D (volume.restrict (Ioi (0 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (continuousOn_const.sub hψc.continuousOn).mul (connesLevyKernelAt_continuousOn α t)
  have hDint_Ioi_delta : IntegrableOn D (Ioi δ) volume := by
    have hmaj : IntegrableOn (fun ε : ℝ => 2 * ε ^ (-1 - α)) (Ioi δ) volume :=
      (integrableOn_Ioi_rpow_of_lt (a := -1 - α) (by linarith) hδ).const_mul 2
    refine MeasureTheory.Integrable.mono' hmaj
      (hDmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hδ.le) le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ε hε
    have hε0 : (0 : ℝ) < ε := lt_trans hδ hε
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn ε hε0)]
    have hcos : 1 - Real.cos (t * ε) ≤ 2 := by
      have := Real.neg_one_le_cos (t * ε)
      linarith
    have hψle : 1 - ψ ε ≤ 1 := by linarith [hψ0 ε]
    have hpow : (0 : ℝ) ≤ ε ^ (-1 - α) := Real.rpow_nonneg hε0.le _
    calc D ε = (1 - ψ ε) * ((1 - Real.cos (t * ε)) * ε ^ (-1 - α)) := rfl
      _ ≤ 1 * ((1 - Real.cos (t * ε)) * ε ^ (-1 - α)) := by
          refine mul_le_mul_of_nonneg_right hψle ?_
          exact mul_nonneg (by linarith [Real.cos_le_one (t * ε)]) hpow
      _ = (1 - Real.cos (t * ε)) * ε ^ (-1 - α) := one_mul _
      _ ≤ 2 * ε ^ (-1 - α) := mul_le_mul_of_nonneg_right hcos hpow
  have hDint_Ioc : IntegrableOn D (Ioc (0 : ℝ) δ) volume := by
    refine (integrable_zero ℝ ℝ _).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ε hε
    exact (hDzero ε hε).symm
  have hDint : IntegrableOn D (Ioi (0 : ℝ)) volume := by
    have hu := hDint_Ioc.union hDint_Ioi_delta
    rwa [show Ioc (0 : ℝ) δ ∪ Ioi δ = Ioi 0 from Ioc_union_Ioi_eq_Ioi hδ.le] at hu
  have hdisj : Disjoint (Ioc (0 : ℝ) δ) (Ioi δ) := by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact absurd hx.2 (not_le.mpr hx')
  have hsplit : (∫ ε in Ioi (0 : ℝ), D ε)
      = (∫ ε in Ioc (0 : ℝ) δ, D ε) + ∫ ε in Ioi δ, D ε := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hDint_Ioc hDint_Ioi_delta,
      show Ioc (0 : ℝ) δ ∪ Ioi δ = Ioi 0 from Ioc_union_Ioi_eq_Ioi hδ.le]
  have hzero : (∫ ε in Ioc (0 : ℝ) δ, D ε) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => hDzero x hx)]
    simp
  have hbound : (∫ ε in Ioi δ, D ε) ≤ 2 * δ ^ (-α) / α := by
    have hmaj : IntegrableOn (fun ε : ℝ => 2 * ε ^ (-1 - α)) (Ioi δ) volume :=
      (integrableOn_Ioi_rpow_of_lt (a := -1 - α) (by linarith) hδ).const_mul 2
    have hle : (∫ ε in Ioi δ, D ε) ≤ ∫ ε in Ioi δ, 2 * ε ^ (-1 - α) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hmaj ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ε hε
        exact hDnn ε (lt_trans hδ hε)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ε hε
        have hε0 : (0 : ℝ) < ε := lt_trans hδ hε
        have hcos : 1 - Real.cos (t * ε) ≤ 2 := by
          have := Real.neg_one_le_cos (t * ε)
          linarith
        have hψle : 1 - ψ ε ≤ 1 := by linarith [hψ0 ε]
        have hpow : (0 : ℝ) ≤ ε ^ (-1 - α) := Real.rpow_nonneg hε0.le _
        calc D ε = (1 - ψ ε) * ((1 - Real.cos (t * ε)) * ε ^ (-1 - α)) := rfl
          _ ≤ 1 * ((1 - Real.cos (t * ε)) * ε ^ (-1 - α)) := by
              refine mul_le_mul_of_nonneg_right hψle ?_
              exact mul_nonneg (by linarith [Real.cos_le_one (t * ε)]) hpow
          _ = (1 - Real.cos (t * ε)) * ε ^ (-1 - α) := one_mul _
          _ ≤ 2 * ε ^ (-1 - α) := mul_le_mul_of_nonneg_right hcos hpow
    have hval : (∫ ε in Ioi δ, 2 * ε ^ (-1 - α)) = 2 * δ ^ (-α) / α := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hδ]
      have h1 : (-1 - α + 1 : ℝ) = -α := by ring
      rw [h1]
      field_simp
    rwa [hval] at hle
  rw [hsplit, hzero, zero_add]
  exact hbound

/-- **§VII (41), the multiplier growth.**  The truncated symbol integral still grows like `t^α`:
the truncation costs at most the fixed constant `2δ^{-α}/α`. -/
theorem connes_truncatedLevy_lower_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hψδ : ∀ x ∈ Ioc (0 : ℝ) δ, ψ x = 1)
    {t : ℝ} (ht : 0 < t) :
    connesLevyConstant α * t ^ α - 2 * δ ^ (-α) / α ≤ connesTruncatedLevy α ψ t := by
  set D : ℝ → ℝ := fun ε => (1 - ψ ε) * connesLevyKernelAt α t ε with hD
  have hSint : IntegrableOn (connesLevyKernelAt α t) (Ioi (0 : ℝ)) volume :=
    connes_levyAt_integrableOn hα0 hα2 t
  have hDnn : ∀ ε : ℝ, 0 < ε → 0 ≤ D ε := fun ε hε =>
    mul_nonneg (by linarith [hψ1 ε]) (connesLevyKernelAt_nonneg α t hε.le)
  have hDmeas : AEStronglyMeasurable D (volume.restrict (Ioi (0 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (continuousOn_const.sub hψc.continuousOn).mul (connesLevyKernelAt_continuousOn α t)
  have hDint : IntegrableOn D (Ioi (0 : ℝ)) volume := by
    refine MeasureTheory.Integrable.mono' hSint hDmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn ε hε0)]
    have hψle : 1 - ψ ε ≤ 1 := by linarith [hψ0 ε]
    calc D ε ≤ 1 * connesLevyKernelAt α t ε :=
          mul_le_mul_of_nonneg_right hψle (connesLevyKernelAt_nonneg α t hε0.le)
      _ = connesLevyKernelAt α t ε := one_mul _
  have hdiff : connesTruncatedLevy α ψ t
      = (∫ ε in Ioi (0 : ℝ), connesLevyKernelAt α t ε) - ∫ ε in Ioi (0 : ℝ), D ε := by
    rw [← MeasureTheory.integral_sub hSint hDint]
    refine setIntegral_congr_fun measurableSet_Ioi fun ε _ => ?_
    simp only [hD]
    ring
  have hmain : (∫ ε in Ioi (0 : ℝ), connesLevyKernelAt α t ε)
      = connesLevyConstant α * t ^ α := connes_levy_scaling ht
  have hdef := connes_levy_truncation_defect_le hα0 hψc hψ0 hψ1 hδ hψδ t
  rw [hdiff, hmain]
  linarith

end

end GaloisForLFunctions.RHTower
