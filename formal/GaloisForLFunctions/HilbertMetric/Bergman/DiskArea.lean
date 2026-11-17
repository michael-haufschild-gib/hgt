import GaloisForLFunctions.HilbertMetric.Bergman.DiskCoefficients
import GaloisForLFunctions.CompactHyperbolicSurfaces.BergmanKernel

/-!
# Exact area norm of the Bergman coefficient model

Gutzmer's circle identity and nonnegative polar integration identify the
coefficient Hilbert norm with normalized area on the open disk. Tonelli's
theorem proves integrability before any Bochner integral is evaluated.
-/

open MeasureTheory Set Filter Metric Complex Real
open scoped ENNReal BigOperators
namespace GaloisForLFunctions.HilbertMetric.Bergman
open HTGeometry CompactHyperbolicSurfaces
noncomputable section

private theorem coefficient_norm_sq (a : Disk) (n : ℕ) :
    ‖coefficient a n‖ ^ 2 = ((n : ℝ) + 1) * ‖a n‖ ^ 2 := by
  rw [coefficient, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

/-- Radial contribution of one orthonormal Bergman coordinate. -/
def radialTerm (a : Disk) (n : ℕ) (r : ℝ) : ℝ :=
  (2 * π * ((n : ℝ) + 1) * ‖a n‖ ^ 2) * r ^ (2 * n + 1)

private theorem radialTerm_integrable (a : Disk) (n : ℕ) :
    IntegrableOn (radialTerm a n) (Ioo 0 1) :=
  (show Continuous (radialTerm a n) by unfold radialTerm; fun_prop).continuousOn.integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

private theorem integral_radialTerm (a : Disk) (n : ℕ) :
    ∫ r in Ioo (0 : ℝ) 1, radialTerm a n r = π * ‖a n‖ ^ 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  unfold radialTerm
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp (disch := positivity)
  ring

private theorem hasSum_radialTerm (a : Disk) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n => radialTerm a n r)
      (r * ∫ θ in (0 : ℝ)..(2 * π), ‖diskFun a (circleMap 0 r θ)‖ ^ 2) := by
  have h := (hasSum_circleAverage_normSq_diskCoeff (differentiableOn_diskFun a) hr0 hr1).mul_left
    (2 * π * r)
  have he (I : ℝ) : (2 * π * r) * ((2 * π)⁻¹ * I) = r * I := by
    field_simp [Real.pi_ne_zero]
  rw [he] at h
  exact h.congr_fun fun n => by
    rw [diskCoeff_diskFun, coefficient_norm_sq, radialTerm, pow_succ]
    ring

private theorem circle_norm_sq_continuous (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun θ : ℝ => ‖f (circleMap 0 r θ)‖ ^ 2) := by
  have h := hf.continuousOn.comp_continuous
    (show Continuous (circleMap 0 r) by unfold circleMap; fun_prop) (fun θ => ?_)
  · exact h.norm.pow 2
  · rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1

private theorem circle_norm_sq_integrable (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntegrableOn (fun θ : ℝ => ‖f (circleMap 0 r θ)‖ ^ 2) (Ioo (-π) π) :=
  (circle_norm_sq_continuous f hf hr0 hr1).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem circle_integral_shift (f : ℂ → ℂ) (r : ℝ) :
    (∫ θ in Ioo (-π) π, ‖f (circleMap 0 r θ)‖ ^ 2) =
      ∫ θ in (0 : ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith only [Real.pi_pos])]
  have h := ((periodic_circleMap 0 r).comp (fun z => ‖f z‖ ^ 2)).intervalIntegral_add_eq
    (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h
  exact h

private theorem lintegral_ball_polar (g : ℂ → ℝ≥0∞) (r : ℝ) :
    ∫⁻ z in ball (0 : ℂ) r, g z =
      ∫⁻ p in Ioo 0 r ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p) := by
  have hS : MeasurableSet (Ioo 0 r ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have hs : Ioo 0 r ×ˢ Ioo (-π) π ⊆ Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  rw [← lintegral_indicator measurableSet_ball,
    ← Complex.lintegral_comp_polarCoord_symm ((ball (0 : ℂ) r).indicator g),
    ← Set.inter_eq_left.mpr hs, ← setLIntegral_indicator hS]
  apply setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
  intro p hp
  rw [Complex.polarCoord_target] at hp
  have hi : Complex.polarCoord.symm p ∈ ball (0 : ℂ) r ↔
      p ∈ Ioo 0 r ×ˢ Ioo (-π) π := by
    rw [mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    exact ⟨fun h => ⟨⟨hp.1, h⟩, hp.2⟩, fun h => h.1.2⟩
  dsimp only
  by_cases h : p ∈ Ioo 0 r ×ˢ Ioo (-π) π
  · rw [indicator_of_mem (hi.mpr h), indicator_of_mem h]
    rfl
  · rw [indicator_of_notMem (fun h' => h (hi.mp h')), indicator_of_notMem h, smul_zero]

private theorem radial_lintegral (a : Disk) :
    (∫⁻ r in Ioo (0 : ℝ) 1, ∑' n, ENNReal.ofReal (radialTerm a n r)) =
      ENNReal.ofReal (π * ‖a‖ ^ 2) := by
  rw [lintegral_tsum (fun n =>
    (show Measurable (radialTerm a n) by unfold radialTerm; fun_prop).ennreal_ofReal.aemeasurable)]
  have hi (n : ℕ) : (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (radialTerm a n r)) =
      ENNReal.ofReal (π * ‖a n‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (radialTerm_integrable a n) ?_, integral_radialTerm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hr0 : 0 ≤ r := hr.1.le
    dsimp [radialTerm]
    positivity
  simp_rw [hi]
  have hs : Summable (fun n => ‖a n‖ ^ 2) := by
    have h := lp.memℓp a
    rw [memℓp_gen_iff (by norm_num)] at h
    refine h.congr fun n => ?_
    rw [← Real.rpow_natCast ‖a n‖ 2]
    norm_num
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hs.mul_left π),
    tsum_mul_left, ← hardyDisk_norm_sq]


/-- Nonnegative polar integration for every function holomorphic on the open disk. -/
theorem holomorphic_lintegral_polar (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1)) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖f z‖ ^ 2)) =
      ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal
        (r * ∫ θ in (0 : ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by
  let S : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (-π) π
  let F : ℝ × ℝ → ℝ := fun p => p.1 * ‖f (circleMap 0 p.1 p.2)‖ ^ 2
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hmaps : MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) S (ball 0 1) := by
    intro p hp
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hp.1.1]
    exact hp.1.2
  have hcont : ContinuousOn F S := by
    apply ContinuousOn.mul continuous_fst.continuousOn
    exact (hf.continuousOn.comp
      (Continuous.continuousOn (by unfold circleMap; fun_prop)) hmaps).norm.pow 2
  have hm : AEMeasurable (fun p => ENNReal.ofReal (F p))
      ((volume.prod volume).restrict S) := by
    rw [← Measure.volume_eq_prod]
    exact (hcont.aestronglyMeasurable hS).aemeasurable.ennreal_ofReal
  rw [lintegral_ball_polar]
  have hbox : ∀ p ∈ S,
      ENNReal.ofReal p.1 * ENNReal.ofReal (‖f (Complex.polarCoord.symm p)‖ ^ 2) =
        ENNReal.ofReal (F p) := by
    intro p hp
    rw [polarCoord_symm_eq_circleMap, ← ENNReal.ofReal_mul hp.1.1.le]
  rw [setLIntegral_congr_fun hS hbox, Measure.volume_eq_prod, setLIntegral_prod _ hm]
  calc
    (∫⁻ r in Ioo (0 : ℝ) 1, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (F (r, θ))) =
        ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal
          (r * ∫ θ in (0 : ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      change (∫⁻ θ in Ioo (-π) π, ENNReal.ofReal
        (r * ‖f (circleMap 0 r θ)‖ ^ 2)) = _
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((circle_norm_sq_integrable f hf hr.1.le hr.2).const_mul r) ?_,
        integral_const_mul, circle_integral_shift]
      filter_upwards with θ
      exact mul_nonneg hr.1.le (sq_nonneg _)

/-- Tonelli and polar coordinates identify the full disk mass as a finite extended real. -/
theorem lintegral_diskFun_norm_sq (a : Disk) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖diskFun a z‖ ^ 2)) =
      ENNReal.ofReal (π * ‖a‖ ^ 2) := by
  rw [holomorphic_lintegral_polar (diskFun a) (differentiableOn_diskFun a)]
  calc
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, ∑' n, ENNReal.ofReal (radialTerm a n r) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      change ENNReal.ofReal (r * ∫ θ in (0 : ℝ)..(2 * π),
        ‖diskFun a (circleMap 0 r θ)‖ ^ 2) = ∑' n, ENNReal.ofReal (radialTerm a n r)
      rw [← (hasSum_radialTerm a hr.1.le hr.2).tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun n => ?_)
          (hasSum_radialTerm a hr.1.le hr.2).summable]
      unfold radialTerm
      have hr0 : 0 ≤ r := hr.1.le
      positivity
    _ = _ := radial_lintegral a

/-- Every coefficient vector gives a genuinely square-integrable holomorphic disk function. -/
theorem integrable_diskFun_norm_sq (a : Disk) :
    IntegrableOn (fun z => ‖diskFun a z‖ ^ 2) (ball (0 : ℂ) 1) := by
  have hm : AEStronglyMeasurable (fun z => ‖diskFun a z‖ ^ 2)
      (volume.restrict (ball (0 : ℂ) 1)) :=
    ((differentiableOn_diskFun a).continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_ball
  apply (lintegral_ofReal_ne_top_iff_integrable hm
    (Filter.Eventually.of_forall fun z => sq_nonneg ‖diskFun a z‖)).mp
  rw [lintegral_diskFun_norm_sq]
  exact ENNReal.ofReal_ne_top

/-- Disk area is exactly π times the coefficient Hilbert norm squared. -/
theorem integral_diskFun_norm_sq (a : Disk) :
    (∫ z in ball (0 : ℂ) 1, ‖diskFun a z‖ ^ 2) = π * ‖a‖ ^ 2 := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_diskFun_norm_sq a)
    (Filter.Eventually.of_forall fun z => sq_nonneg ‖diskFun a z‖)
  rw [lintegral_diskFun_norm_sq] at h
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (sq_nonneg ‖a‖))] using ht

/-- Normalized disk area recovers the Hilbert norm without any auxiliary hypotheses. -/
theorem normalized_area_norm (a : Disk) :
    (π⁻¹ * ∫ z in ball (0 : ℂ) 1, ‖diskFun a z‖ ^ 2) = ‖a‖ ^ 2 := by
  rw [integral_diskFun_norm_sq, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

#print axioms holomorphic_lintegral_polar
#print axioms lintegral_diskFun_norm_sq
#print axioms integrable_diskFun_norm_sq
#print axioms integral_diskFun_norm_sq
#print axioms normalized_area_norm
end
end GaloisForLFunctions.HilbertMetric.Bergman
