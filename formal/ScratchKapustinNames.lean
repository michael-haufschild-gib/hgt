import GaloisForLFunctions.HTGeometry.HardyDiskMultiplier
import GaloisForLFunctions.HTGeometry.HerglotzDiscDilation

open Complex Filter Metric Real Topology intervalIntegral MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem scratch_circleAverage_normSq_le_of_re_bounded
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hg0 : g 0 = 0) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, |(g z).re| ≤ C)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ‖g (circleMap 0 r θ)‖ ^ 2 ≤ 2 * C ^ 2 := by
  by_cases hr : r = 0
  · subst r
    simp [hg0]
    positivity
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
  have hsqDiff : DifferentiableOn ℂ (fun z => g z ^ 2) (ball (0 : ℂ) 1) :=
    hg.pow 2
  have hgCircle : Continuous fun theta : ℝ => g (circleMap 0 r theta) := by
    rw [continuous_iff_continuousAt]
    intro theta
    have hzmem : circleMap 0 r theta ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, norm_circleMap_zero]
      exact abs_lt.mpr ⟨by linarith, hr1⟩
    exact (hg.differentiableAt (isOpen_ball.mem_nhds hzmem)).continuousAt.comp
      (by fun_prop)
  have hmean := circleAverage_dilate_eq_center hrpos hr1 hsqDiff
  rw [hg0, zero_pow (by norm_num : 2 ≠ 0)] at hmean
  have hmeanInt :
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (g (circleMap 0 r θ) ^ 2).re = 0 := by
    have hmean' :
        (2 * Real.pi)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              g (circleMap 0 r θ) ^ 2 = 0 := by
      simpa [Real.circleAverage, circleMap, mul_comm] using hmean
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    have hintComplex :
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
            g (circleMap 0 r θ) ^ 2 = 0 := by
      apply (mul_eq_zero.mp hmean').resolve_left
      simpa using inv_ne_zero hpi
    have hintIntegrable : IntervalIntegrable
        (fun θ : ℝ => g (circleMap 0 r θ) ^ 2) volume 0 (2 * Real.pi) := by
      exact (hgCircle.pow 2).intervalIntegrable _ _
    have hre := ContinuousLinearMap.intervalIntegral_comp_comm
      Complex.reCLM hintIntegrable
    rw [Complex.reCLM_apply, hintComplex] at hre
    change (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.reCLM (g (circleMap 0 r θ) ^ 2)) = 0
    exact hre
  have hboundPoint (theta : ℝ) :
      ‖g (circleMap 0 r theta)‖ ^ 2 ≤
        2 * C ^ 2 - (g (circleMap 0 r theta) ^ 2).re := by
    have hzmem : circleMap 0 r theta ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, norm_circleMap_zero]
      exact abs_lt.mpr ⟨by linarith, hr1⟩
    have hre := hC _ hzmem
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hre
    have hreSq : (g (circleMap 0 r theta)).re ^ 2 ≤ C ^ 2 := by
      calc
        (g (circleMap 0 r theta)).re ^ 2 =
            |(g (circleMap 0 r theta)).re| *
              |(g (circleMap 0 r theta)).re| := by
                rw [← sq_abs]
                ring
        _ ≤ C * C := mul_le_mul hre hre (abs_nonneg _) hC0
        _ = C ^ 2 := by ring
    have hid : ‖g (circleMap 0 r theta)‖ ^ 2 =
        2 * (g (circleMap 0 r theta)).re ^ 2 -
          (g (circleMap 0 r theta) ^ 2).re := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, pow_two, Complex.mul_re]
      ring
    rw [hid]
    linarith
  have hnormInt : IntervalIntegrable
      (fun theta : ℝ => ‖g (circleMap 0 r theta)‖ ^ 2) volume 0 (2 * Real.pi) :=
    (hgCircle.norm.pow 2).intervalIntegrable _ _
  have hupperInt : IntervalIntegrable
      (fun theta : ℝ => 2 * C ^ 2 - (g (circleMap 0 r theta) ^ 2).re)
        volume 0 (2 * Real.pi) :=
    (continuous_const.sub
      (Complex.continuous_re.comp (hgCircle.pow 2))).intervalIntegrable _ _
  have hconstInt : IntervalIntegrable (fun _theta : ℝ => 2 * C ^ 2)
      volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hreInt : IntervalIntegrable
      (fun theta : ℝ => (g (circleMap 0 r theta) ^ 2).re)
        volume 0 (2 * Real.pi) :=
    (Complex.continuous_re.comp (hgCircle.pow 2)).intervalIntegrable _ _
  calc
    (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖g (circleMap 0 r θ)‖ ^ 2 ≤
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (2 * C ^ 2 - (g (circleMap 0 r θ) ^ 2).re) := by
          gcongr
          exact intervalIntegral.integral_mono_on (by positivity)
            hnormInt hupperInt
            (fun theta _ => hboundPoint theta)
    _ = 2 * C ^ 2 := by
      rw [intervalIntegral.integral_sub hconstInt hreInt,
        intervalIntegral.integral_const, hmeanInt]
      field_simp [Real.pi_ne_zero]
      ring

theorem scratch_summable_diskCoeff_sq_of_re_bounded
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hg0 : g 0 = 0) {C : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, |(g z).re| ≤ C) :
    Summable (fun n => ‖diskCoeff g n‖ ^ 2) := by
  exact (summable_diskCoeff_sq_of_circleAverage_le hg
    (r₀ := 0) (K := 2 * C ^ 2) (by norm_num) (by norm_num)
    (fun r _ hr1 => scratch_circleAverage_normSq_le_of_re_bounded
      hg hg0 hC (by positivity) hr1)).1

end GaloisForLFunctions.HTGeometry
