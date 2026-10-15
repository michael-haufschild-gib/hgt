import GaloisForLFunctions.HTGeometry.ArctanSqrtAntiderivative
import GaloisForLFunctions.RHTower.LogSineQuantileProfile
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Positive resolvent representation of the logarithmic sine profile

The literal scalar lift is an absolutely integrable Stieltjes mixture with density
`(1 + delta / 2 * log(1 + 1 / s)) / (pi * sqrt s)`. This density is positive for
nonnegative delta. The proof integrates elementary resolvents over the auxiliary
parameter `(0,1)` and justifies Fubini across the singular endpoints. The final
pairing theorem transfers each cosine coefficient to the same positive mixture.

This supplies the source identity needed to test conductance Hankel positivity
against GTA's nonnormal coupling. It asserts neither real spectrum nor a completed
counterexample to spectral sufficiency; those require further source theorems.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

private def rootStieltjesKernel (r v s : ℝ) : ℝ :=
  r ^ 2 * v / (Real.pi * (r ^ 2 + s) * Real.sqrt s * (s + v ^ 2))

private theorem integrableOn_rootResolvent {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => 1 / ((a + s) * Real.sqrt s)) (Ioi 0) := by
  by_contra h
  have he := integral_undef h
  rw [GaloisForLFunctions.integral_Ioi_one_div_add_mul_sqrt ha] at he
  exact (div_ne_zero Real.pi_ne_zero (Real.sqrt_pos.mpr ha).ne') he

private theorem rootStieltjes_gap {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (hne : v ≠ r) :
    v ^ 2 - r ^ 2 ≠ 0 := by
  intro h
  have he : (v - r) * (v + r) = 0 := by nlinarith
  exact hne (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (by positivity)))

private theorem rootStieltjes_partialFractions {r v s : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hne : v ≠ r) (hs : 0 < s) :
    rootStieltjesKernel r v s = (r ^ 2 * v / (Real.pi * (v ^ 2 - r ^ 2))) *
      (1 / ((r ^ 2 + s) * Real.sqrt s) - 1 / ((v ^ 2 + s) * Real.sqrt s)) := by
  have hg := rootStieltjes_gap hr hv hne
  have hsr : r ^ 2 + s ≠ 0 := by positivity
  have hsv : v ^ 2 + s ≠ 0 := by positivity
  have hvs : s + v ^ 2 ≠ 0 := by positivity
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  unfold rootStieltjesKernel
  field_simp [hg, hsr, hsv, hvs, hsq, Real.pi_ne_zero]
  ring

private theorem integrableOn_rootStieltjesKernel {r v : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hne : v ≠ r) :
    IntegrableOn (rootStieltjesKernel r v) (Ioi 0) := by
  have h := ((integrableOn_rootResolvent (pow_pos hr 2)).sub
    (integrableOn_rootResolvent (pow_pos hv 2))).const_mul
      (r ^ 2 * v / (Real.pi * (v ^ 2 - r ^ 2)))
  exact IntegrableOn.congr_fun h (fun s hs => (rootStieltjes_partialFractions hr hv hne hs).symm)
    measurableSet_Ioi

private theorem integral_rootStieltjesKernel {r v : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hne : v ≠ r) :
    (∫ s in Ioi (0 : ℝ), rootStieltjesKernel r v s) = r / (r + v) := by
  have hg := rootStieltjes_gap hr hv hne
  calc
    (∫ s in Ioi (0 : ℝ), rootStieltjesKernel r v s) =
        ∫ s in Ioi (0 : ℝ), (r ^ 2 * v / (Real.pi * (v ^ 2 - r ^ 2))) *
          (1 / ((r ^ 2 + s) * Real.sqrt s) -
            1 / ((v ^ 2 + s) * Real.sqrt s)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact rootStieltjes_partialFractions hr hv hne hs
    _ = (r ^ 2 * v / (Real.pi * (v ^ 2 - r ^ 2))) *
        (Real.pi / r - Real.pi / v) := by
      rw [integral_const_mul, integral_sub
        (integrableOn_rootResolvent (pow_pos hr 2))
        (integrableOn_rootResolvent (pow_pos hv 2)),
        GaloisForLFunctions.integral_Ioi_one_div_add_mul_sqrt (pow_pos hr 2),
        GaloisForLFunctions.integral_Ioi_one_div_add_mul_sqrt (pow_pos hv 2),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hr, abs_of_pos hv]
    _ = r / (r + v) := by
      field_simp [hr.ne', hv.ne', hg, show r + v ≠ 0 by positivity, Real.pi_ne_zero]
      ring

private theorem integral_unit_rootFraction {r : ℝ} (hr : 0 < r) :
    (∫ v in (0 : ℝ)..1, r / (r + v)) = r * Real.log (1 + 1 / r) := by
  have hd : ∀ v ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v => r * Real.log (r + v)) (r / (r + v)) v := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    convert (((hasDerivAt_id v).const_add r).log
      (show r + v ≠ 0 by linarith [hv.1])).const_mul r using 1 <;>
        first | rfl | (simp [div_eq_mul_inv])
  have hi : IntervalIntegrable (fun v => r / (r + v)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun v hv => by linarith [hv.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  have he : 1 + 1 / r = (r + 1) / r := by field_simp
  rw [he, Real.log_div (by positivity) hr.ne']
  simp only [add_zero]
  ring

private theorem integral_unit_parameterFraction {s : ℝ} (hs : 0 < s) :
    (∫ v in (0 : ℝ)..1, v / (s + v ^ 2)) = Real.log (1 + 1 / s) / 2 := by
  have hd : ∀ v ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v => Real.log (s + v ^ 2) / 2) (v / (s + v ^ 2)) v := by
    intro v _
    convert ((((hasDerivAt_id v).pow 2).const_add s).log
      (show s + v ^ 2 ≠ 0 by positivity)).div_const 2 using 1 <;>
        first | rfl | (simp; ring)
  have hi : IntervalIntegrable (fun v => v / (s + v ^ 2)) volume 0 1 := by
    exact (continuous_id.div (continuous_const.add (continuous_id.pow 2))
      (fun v : ℝ => (add_pos_of_pos_of_nonneg hs (sq_nonneg v)).ne')).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  have he : 1 + 1 / s = (s + 1) / s := by field_simp
  rw [he, Real.log_div (by positivity) hs.ne']
  norm_num
  ring

private theorem ae_rootStieltjes_parameter (r : ℝ) :
    ∀ᵐ v : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), 0 < v ∧ v ≠ r := by
  have he : ∀ᵐ v : ℝ ∂volume, v ≠ r := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae he] with v hv hne
  exact ⟨hv.1, hne⟩

private theorem integrable_rootStieltjes_prod {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ => rootStieltjesKernel r p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun p : ℝ × ℝ => rootStieltjesKernel r p.1 p.2) := by
    unfold rootStieltjesKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_rootStieltjes_parameter r] with v hv
    exact integrableOn_rootStieltjesKernel hr hv.1 hv.2
  · have hi : IntegrableOn (fun v : ℝ => r / (r + v)) (Ioo 0 1) := by
      apply IntegrableOn.mono_set (s := Ioo 0 1) (t := Icc 0 1) _ Ioo_subset_Icc_self
      apply ContinuousOn.integrableOn_Icc
      exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
        (fun v hv => by linarith [hv.1])
    apply hi.congr
    filter_upwards [ae_rootStieltjes_parameter r] with v hv
    rw [← integral_rootStieltjesKernel hr hv.1 hv.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hv0 : 0 < v := hv.1
    have hs0 : 0 < s := hs
    exact (Real.norm_of_nonneg (by unfold rootStieltjesKernel; positivity)).symm

private theorem integral_rootStieltjes_parameter {r s : ℝ} (hs : 0 < s) :
    (∫ v in Ioo (0 : ℝ) 1, rootStieltjesKernel r v s) =
      (r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s)) *
        (Real.log (1 + 1 / s) / 2) := by
  have he : (fun v => rootStieltjesKernel r v s) =
      fun v => (r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s)) *
        (v / (s + v ^ 2)) := by
    funext v
    unfold rootStieltjesKernel
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_unit_parameterFraction hs]

private theorem integrableOn_logRootStieltjes {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ =>
      (r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s)) *
        (Real.log (1 + 1 / s) / 2)) (Ioi 0) := by
  apply (integrable_rootStieltjes_prod hr).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact integral_rootStieltjes_parameter hs

private theorem integral_logRootStieltjes {r : ℝ} (hr : 0 < r) :
    (∫ s in Ioi (0 : ℝ),
      (r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s)) *
        (Real.log (1 + 1 / s) / 2)) = r * Real.log (1 + 1 / r) := by
  calc
    _ = ∫ s in Ioi (0 : ℝ), ∫ v in Ioo (0 : ℝ) 1,
        rootStieltjesKernel r v s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (integral_rootStieltjes_parameter hs).symm
    _ = ∫ v in Ioo (0 : ℝ) 1, ∫ s in Ioi (0 : ℝ),
        rootStieltjesKernel r v s :=
      (integral_integral_swap (integrable_rootStieltjes_prod hr)).symm
    _ = ∫ v in Ioo (0 : ℝ) 1, r / (r + v) := by
      apply integral_congr_ae
      filter_upwards [ae_rootStieltjes_parameter r] with v hv
      exact integral_rootStieltjesKernel hr hv.1 hv.2
    _ = r * Real.log (1 + 1 / r) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
        integral_unit_rootFraction hr]

/-- Positive Stieltjes density for the logarithmic sine scalar lift. -/
def logSineStieltjesDensity (δ s : ℝ) : ℝ :=
  (1 + δ / 2 * Real.log (1 + 1 / s)) / (Real.pi * Real.sqrt s)

private theorem integrableOn_baseRootStieltjes {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s))
      (Ioi 0) := by
  have h := (integrableOn_rootResolvent (pow_pos hr 2)).const_mul (r ^ 2 / Real.pi)
  apply Integrable.congr h
  filter_upwards with s
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

private theorem integral_baseRootStieltjes {r : ℝ} (hr : 0 < r) :
    (∫ s in Ioi (0 : ℝ), r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s)) = r := by
  have he : (fun s : ℝ => r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s)) =
      fun s => (r ^ 2 / Real.pi) * (1 / ((r ^ 2 + s) * Real.sqrt s)) := by
    funext s
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [he, integral_const_mul,
    GaloisForLFunctions.integral_Ioi_one_div_add_mul_sqrt (pow_pos hr 2),
    Real.sqrt_sq_eq_abs, abs_of_pos hr]
  field_simp

private theorem logSineStieltjes_split (δ r s : ℝ) :
    r ^ 2 / (r ^ 2 + s) * logSineStieltjesDensity δ s =
      r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s) +
        δ * ((r ^ 2 / (Real.pi * (r ^ 2 + s) * Real.sqrt s)) *
          (Real.log (1 + 1 / s) / 2)) := by
  unfold logSineStieltjesDensity
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Absolute integrability of the scalar Stieltjes representation, for every real parameter. -/
theorem integrableOn_logSineStieltjes {δ r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => r ^ 2 / (r ^ 2 + s) * logSineStieltjesDensity δ s)
      (Ioi 0) := by
  apply ((integrableOn_baseRootStieltjes hr).add
    ((integrableOn_logRootStieltjes hr).const_mul δ)).congr
  filter_upwards with s
  exact (logSineStieltjes_split δ r s).symm

/-- The literal scalar profile equals its explicit Stieltjes integral. -/
theorem logSineLift_eq_stieltjes {δ r : ℝ} (hr : 0 < r) :
    logSineLift δ r =
      ∫ s in Ioi (0 : ℝ), r ^ 2 / (r ^ 2 + s) * logSineStieltjesDensity δ s := by
  simp_rw [logSineStieltjes_split]
  rw [integral_add (integrableOn_baseRootStieltjes hr)
    ((integrableOn_logRootStieltjes hr).const_mul δ), integral_const_mul,
    integral_baseRootStieltjes hr, integral_logRootStieltjes hr, logSineLift_eq hr]
  ring

theorem logSineStieltjesDensity_pos {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 < s) :
    0 < logSineStieltjesDensity δ s := by
  have hl : 0 ≤ Real.log (1 + 1 / s) :=
    Real.log_nonneg (by have := one_div_pos.mpr hs; linarith)
  unfold logSineStieltjesDensity
  positivity

/-- The exact positive resolvent mixture for the profile on its full open interval. -/
theorem logSineProfile_eq_stieltjes {δ t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    logSineProfile δ t = ∫ s in Ioi (0 : ℝ),
      (Real.sin (Real.pi * t)) ^ 2 / ((Real.sin (Real.pi * t)) ^ 2 + s) *
        logSineStieltjesDensity δ s := by
  exact logSineLift_eq_stieltjes (logSineProfile_sine_pos ht)

/-- Joint integrability, including the profile endpoints and the unbounded mixing variable. -/
theorem integrable_logSineStieltjes_prod {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun p : ℝ × ℝ =>
      (Real.sin (Real.pi * p.1)) ^ 2 / ((Real.sin (Real.pi * p.1)) ^ 2 + p.2) *
        logSineStieltjesDensity δ p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (Real.sin (Real.pi * p.1)) ^ 2 / ((Real.sin (Real.pi * p.1)) ^ 2 + p.2) *
        logSineStieltjesDensity δ p.2) := by
    unfold logSineStieltjesDensity
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact integrableOn_logSineStieltjes (logSineProfile_sine_pos ht)
  · apply ((continuousOn_logSineProfile δ).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [logSineProfile_eq_stieltjes ht]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    have hd := (logSineStieltjesDensity_pos hδ hs0).le
    exact (Real.norm_of_nonneg (mul_nonneg (by positivity) hd)).symm

/-- Fubini for the literal profile and each cosine mode. No formal interchange is assumed. -/
theorem logSineProfile_cosine_stieltjes {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1, logSineProfile δ t * Real.cos (2 * Real.pi * n * t)) =
      ∫ s in Ioi (0 : ℝ), logSineStieltjesDensity δ s *
        ∫ t in Ioo (0 : ℝ) 1,
          (Real.sin (Real.pi * t)) ^ 2 / ((Real.sin (Real.pi * t)) ^ 2 + s) *
            Real.cos (2 * Real.pi * n * t) := by
  let K : ℝ × ℝ → ℝ := fun p =>
    (Real.sin (Real.pi * p.1)) ^ 2 / ((Real.sin (Real.pi * p.1)) ^ 2 + p.2) *
      logSineStieltjesDensity δ p.2
  let F : ℝ × ℝ → ℝ := fun p => K p * Real.cos (2 * Real.pi * n * p.1)
  have hK : Integrable K
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    integrable_logSineStieltjes_prod hδ
  have hF : Integrable F
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply hK.norm.mono'
    · have hm : Measurable F := by unfold F K logSineStieltjesDensity; fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards with p
      change ‖K p * Real.cos (2 * Real.pi * n * p.1)‖ ≤ ‖K p‖
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1, ∫ s in Ioi (0 : ℝ), F (t, s) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      simp only [F, K]
      rw [integral_mul_const, ← logSineProfile_eq_stieltjes ht]
    _ = ∫ s in Ioi (0 : ℝ), ∫ t in Ioo (0 : ℝ) 1, F (t, s) :=
      integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp [F, K]
      ring

end
end RHTower
