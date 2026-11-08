import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartitionAngularBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainIncompleteSeed
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellinConvergence
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral

/-!
# Absolute convergence of the incomplete Narain seed

The positive angular majorant and actual scalar Mellin convergence give
strip integrability throughout `Re s > 1`. Height truncation controls
the vacuum term, and the hyperbolic chart supplies the measure factor.
-/

open Complex RHTower Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Absolute scalar Mellin convergence supplies the height-integrated angular majorant. -/
theorem integrable_narainScalarHeat_norm_weight (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun y : ℝ => y ^ (a - 1) * ‖narainScalarHeat ρ σ y‖) (Ioi 0) := by
  have h := (mellinConvergent_narainScalarHeat ρ σ (s := (a : ℂ)) (by simpa using ha)).norm
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- Truncation makes the vacuum term integrable; the nonvacuum term uses the actual scalar source. -/
theorem integrable_narainScalarHeat_truncated_majorant (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {a T : ℝ} (ha : 1 < a) :
    IntegrableOn (fun y : ℝ => if y ≤ T then
      y ^ (a - 1) * (1 + ‖narainScalarHeat ρ σ y‖) else 0) (Ioi 0) := by
  have ha0 : 0 ≤ a - 1 := by linarith only [ha]
  have hc : Continuous (fun y : ℝ => y ^ (a - 1)) := by fun_prop
  have hvac : Integrable ((Ioc (0 : ℝ) T).indicator (fun y => y ^ (a - 1))) :=
    ((hc.intervalIntegrable 0 T).1).integrable_indicator measurableSet_Ioc
  have hheat := (integrable_narainScalarHeat_norm_weight ρ σ ha).indicator
    (measurableSet_Iic : MeasurableSet (Iic T))
  refine (hvac.integrableOn.add hheat).congr_fun ?_ measurableSet_Ioi
  intro y hy
  simp only [Pi.add_apply]
  by_cases hT : y ≤ T
  · rw [indicator_of_mem (show y ∈ Ioc (0 : ℝ) T from ⟨hy, hT⟩),
      indicator_of_mem (show y ∈ Iic T from hT), if_pos hT]
    ring
  · rw [indicator_of_notMem (show y ∉ Ioc (0 : ℝ) T from fun h => hT h.2),
      indicator_of_notMem (show y ∉ Iic T from hT), if_neg hT, zero_add]

/-- The angular majorant proves absolute convergence of the truncated chart throughout `Re s>1`. -/
theorem integrable_narainIncompleteSeed_chart (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) (T : ℝ) :
    Integrable (fun p : ℝ × ℝ => if p.1 ≤ T then
      (p.1 : ℂ) ^ (s - 2) * narainPartition ρ σ p.2 p.1 else 0)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ico (0 : ℝ) 1))) := by
  let f : ℝ × ℝ → ℂ := fun p => if p.1 ≤ T then
    (p.1 : ℂ) ^ (s - 2) * narainPartition ρ σ p.2 p.1 else 0
  have hm : Measurable f := by
    apply Measurable.ite (measurableSet_le measurable_fst measurable_const)
    · exact (by fun_prop : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (s - 2))).mul
        ((measurable_narainPartition ρ σ).comp measurable_swap)
    · exact measurable_const
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hx : IntegrableOn (fun x : ℝ => narainPartition ρ σ x y) (Ico 0 1) :=
      (continuous_narainPartition_fixedHeight ρ σ hy).integrableOn_Icc.mono_set Ico_subset_Icc_self
    by_cases hT : y ≤ T
    · simpa only [f, if_pos hT] using hx.const_mul ((y : ℂ) ^ (s - 2))
    · simp only [f, if_neg hT]
      exact integrable_const (0 : ℂ)
  · apply (integrable_narainScalarHeat_truncated_majorant
      ⟨0, ρ.y, ρ.y_pos⟩ σ (T := T) hs).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    by_cases hT : y ≤ T
    · simp only [f, if_pos hT, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, integral_const_mul,
        integral_Ico_eq_integral_Ioc]
      have he : y ^ (s.re - 2) * y = y ^ (s.re - 1) := by
        calc
          _ = y ^ (s.re - 2) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = y ^ ((s.re - 2) + 1) := (Real.rpow_add hy _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ ≤ y ^ (s.re - 2) * (y * (1 + ‖narainScalarHeat ⟨0, ρ.y, ρ.y_pos⟩ σ y‖)) :=
          mul_le_mul_of_nonneg_left (integral_norm_narainPartition_le ρ σ hy)
            (Real.rpow_nonneg (le_of_lt hy) _)
        _ = _ := by rw [← mul_assoc, he]
    · simp only [f, if_neg hT, norm_zero, integral_zero]
      exact le_rfl

/-- Absolute convergence of the actual incomplete seed on the hyperbolic strip. -/
theorem integrableOn_narainIncompleteSeed (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) (T : ℝ) :
    IntegrableOn (narainIncompleteSeed ρ σ s T) modularStrip := by
  apply (integrableOn_modularStrip_iff _).mpr
  have h := integrable_narainIncompleteSeed_chart ρ σ hs T
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have h' : IntegrableOn (fun p : ℝ × ℝ => if p.1 ≤ T then
      (p.1 : ℂ) ^ (s - 2) * narainPartition ρ σ p.2 p.1 else 0)
      (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) := h
  refine h'.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ico)
  intro p hp
  have hy : 0 < p.1 := hp.1
  simp only [stripChartIntegrand, narainIncompleteSeed, narainPartitionOnUpperHalfPlane,
    UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨p.2, p.1⟩ : ℂ).im from hy)]
  change (if p.1 ≤ T then (p.1 : ℂ) ^ (s - 2) * narainPartition ρ σ p.2 p.1 else 0) =
    (p.1 ^ 2)⁻¹ • (if p.1 ≤ T then (p.1 : ℂ) ^ s * narainPartition ρ σ p.2 p.1 else 0)
  by_cases hT : p.1 ≤ T
  · simp only [if_pos hT, Complex.real_smul]
    have hw : (((p.1 ^ 2)⁻¹ : ℝ) : ℂ) * (p.1 : ℂ) ^ s = (p.1 : ℂ) ^ (s - 2) := by
      rw [Complex.ofReal_inv, Complex.ofReal_pow, Complex.cpow_sub _ _
        (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.cpow_ofNat]
      ring
    rw [← mul_assoc, hw]
  · simp only [if_neg hT, smul_zero]

#print axioms integrable_narainScalarHeat_truncated_majorant
#print axioms integrableOn_narainIncompleteSeed
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
