import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBetaBound

/-!
# A uniform complex Beta-integral bound

When the second Beta parameter has real part at least one, its factor on the
unit interval has norm at most one.  Thus the complex Beta integral is bounded
by the elementary endpoint value `1 / Re u`, uniformly in both imaginary
parts.  This is the form needed to turn a reflected Barnes left edge into a
fixed-degree polynomial times its geometric radial factor.
-/

open Complex MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- If the second parameter has real part at least one, the complex Beta
integral is at most `1 / Re u` in norm. -/
theorem norm_betaIntegral_le_inv_re {u v : ℂ} (hu : 0 < u.re) (hv : 1 ≤ v.re) :
    ‖Complex.betaIntegral u v‖ ≤ 1 / u.re := by
  have hzero : (0 : ℝ) ≤ 1 := by norm_num
  have hvpos : 0 < v.re := lt_of_lt_of_le zero_lt_one hv
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ ((u.re : ℂ) - 1) * (1 - (x : ℂ)) ^ ((1 : ℂ) - 1)
  have hf : IntervalIntegrable f volume 0 1 := by
    simpa [f] using Complex.betaIntegral_convergent (u := u) (v := v) hu hvpos
  have hg : IntervalIntegrable g volume 0 1 := by
    simpa [g] using Complex.betaIntegral_convergent (u := (u.re : ℂ)) (v := (1 : ℂ))
      (by simpa using hu) (by norm_num)
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) 1, ‖f x‖ ≤ ‖g x‖ := by
    intro x hx
    rw [show f x = (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) by rfl,
      show g x = (x : ℂ) ^ ((u.re : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((1 : ℂ) - 1) by rfl,
      norm_betaIntegrand hx,
      norm_betaIntegrand (u := (u.re : ℂ)) (v := (1 : ℂ)) hx]
    simp only [ofReal_re, one_re, sub_zero, Real.rpow_zero, mul_one]
    have hbase : 0 ≤ x ^ (u.re - 1) := Real.rpow_nonneg (le_of_lt hx.1) _
    have hfactor : (1 - x) ^ (v.re - 1) ≤ 1 := by
      apply Real.rpow_le_one
      · linarith [hx.2]
      · linarith [hx.1]
      · linarith
    calc
      x ^ (u.re - 1) * (1 - x) ^ (v.re - 1)
          ≤ x ^ (u.re - 1) * 1 := mul_le_mul_of_nonneg_left hfactor hbase
      _ = x ^ (u.re - 1) := by ring
  have hmono : (∫ x in (0 : ℝ)..1, ‖f x‖) ≤ ∫ x in (0 : ℝ)..1, ‖g x‖ :=
    intervalIntegral.integral_mono_on_of_le_Ioo hzero hf.norm hg.norm hpoint
  have hgnorm : (∫ x in (0 : ℝ)..1, ‖g x‖) = 1 / u.re := by
    have hnorm : (∫ x in (0 : ℝ)..1, ‖g x‖) =
        ∫ x in (0 : ℝ)..1, x ^ (u.re - 1) := by
      rw [intervalIntegral.integral_of_le hzero, intervalIntegral.integral_of_le hzero]
      refine MeasureTheory.integral_congr_ae ?_
      have hmeas : (volume.restrict (Ioc (0 : ℝ) 1)) {(1 : ℝ)} = 0 := by simp
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.compl_mem_ae_iff.mpr hmeas] with x hx hx1
      have hxIoo : x ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩
        simpa using hx1
      rw [show g x = (x : ℂ) ^ ((u.re : ℂ) - 1) *
          (1 - (x : ℂ)) ^ ((1 : ℂ) - 1) by rfl,
        norm_betaIntegrand (u := (u.re : ℂ)) (v := (1 : ℂ)) hxIoo]
      simp
    have hcast : Complex.betaIntegral (u.re : ℂ) (1 : ℂ) =
        (((∫ x in (0 : ℝ)..1, x ^ (u.re - 1)) : ℝ) : ℂ) := by
      rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal,
        intervalIntegral.integral_of_le hzero, intervalIntegral.integral_of_le hzero]
      refine MeasureTheory.integral_congr_ae ?_
      have hmeas : (volume.restrict (Ioc (0 : ℝ) 1)) {(1 : ℝ)} = 0 := by simp
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
        MeasureTheory.compl_mem_ae_iff.mpr hmeas] with x hx hx1
      have hxIoo : x ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩
        simpa using hx1
      rw [betaIntegrand_ofReal (a := u.re) (b := 1) hxIoo]
      simp
    have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..1, x ^ (u.re - 1) := by
      refine intervalIntegral.integral_nonneg hzero ?_
      intro x hx
      exact Real.rpow_nonneg hx.1 _
    have hbeta := Complex.betaIntegral_eval_one_right (u := (u.re : ℂ)) (by simpa using hu)
    calc
      (∫ x in (0 : ℝ)..1, ‖g x‖) = ∫ x in (0 : ℝ)..1, x ^ (u.re - 1) := hnorm
      _ = ‖Complex.betaIntegral (u.re : ℂ) (1 : ℂ)‖ := by
        rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ = ‖1 / ((u.re : ℝ) : ℂ)‖ := by rw [hbeta]
      _ = 1 / u.re := by
        rw [norm_div, Complex.norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  rw [Complex.betaIntegral]
  exact (intervalIntegral.norm_integral_le_integral_norm hzero).trans (hmono.trans_eq hgnorm)

end

end GaloisForLFunctions.HTGeometry
