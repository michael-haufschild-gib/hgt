import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailRepresentation

/-!
# The exact aperture primitive

Triangular Fubini converts an aperture-weighted center tail into the
literal integral weighted by `s * sinh (a * s)`. Absolute convergence
follows from the same weighted integral.
-/

set_option autoImplicit false

open MeasureTheory Set Complex Filter Topology
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower
noncomputable section

private theorem continuous_apertureWeight (a : ℝ) : Continuous (thetaCuspCenterTailWeight a) := by
  unfold thetaCuspCenterTailWeight
  fun_prop

private theorem hasDerivAt_aperturePrimitive (a r : ℝ) :
    HasDerivAt (fun s : ℝ => s * Real.sinh (a * s)) (thetaCuspCenterTailWeight a r) r := by
  have h := (hasDerivAt_id r).mul
    ((Real.hasDerivAt_sinh (a * r)).comp r ((hasDerivAt_id r).const_mul a))
  convert h using 1
  all_goals first | rfl | (dsimp only [thetaCuspCenterTailWeight, Function.comp_apply, id_eq]; ring)

private theorem integral_apertureWeight_Ioo (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ r in Ioo (0 : ℝ) s, thetaCuspCenterTailWeight a r) = s * Real.sinh (a * s) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
    (fun r _ => hasDerivAt_aperturePrimitive a r)
    ((continuous_apertureWeight a).intervalIntegrable 0 s)
  simpa only [mul_zero, zero_mul, sub_zero] using h

/-- Integrating the aperture weight over the center triangle gives its exact primitive. -/
theorem integral_apertureWeight_mul_tail {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ}
    (hg : StronglyMeasurable g)
    (hi : IntegrableOn (fun s => s * Real.sinh (a * s) * g s) (Ioi 0)) :
    (∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r * (∫ s in Ioi r, g s)) =
      ∫ s in Ioi (0 : ℝ), s * Real.sinh (a * s) * g s := by
  classical
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let D : Set (ℝ × ℝ) := {p | p.2 < p.1}
  let F : ℝ × ℝ → ℝ := D.indicator
    (fun p => thetaCuspCenterTailWeight a p.2 * g p.1)
  have hD : MeasurableSet D := measurableSet_lt measurable_snd measurable_fst
  have hF : StronglyMeasurable F :=
    (((continuous_apertureWeight a).stronglyMeasurable.comp_measurable measurable_snd).mul
      (hg.comp_measurable measurable_fst)).indicator hD
  have hslice (s : ℝ) : (fun r => F (s, r)) =
      (Iio s).indicator (fun r => thetaCuspCenterTailWeight a r * g s) := rfl
  have hnormslice (s : ℝ) : (fun r => ‖F (s, r)‖) =
      (Iio s).indicator (fun r => ‖thetaCuspCenterTailWeight a r * g s‖) := by
    funext r
    by_cases h : r < s <;> simp [F, D, Set.indicator, h]
  have hinner (s : ℝ) : Integrable (fun r => F (s, r)) μ := by
    rw [hslice, integrable_indicator_iff measurableSet_Iio]
    change Integrable _ ((volume.restrict (Ioi (0 : ℝ))).restrict (Iio s))
    rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
    exact ((continuous_apertureWeight a).integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const (g s)
  have hinner_eq (s : ℝ) :
      (∫ r, F (s, r) ∂μ) =
        (∫ r in Ioo (0 : ℝ) s, thetaCuspCenterTailWeight a r) * g s := by
    rw [hslice, integral_indicator measurableSet_Iio]
    change (∫ r, _ ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Iio s))) = _
    rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, integral_mul_const]
  have hinner_norm (s : ℝ) :
      (∫ r, ‖F (s, r)‖ ∂μ) =
        (∫ r in Ioo (0 : ℝ) s, thetaCuspCenterTailWeight a r) * |g s| := by
    rw [hnormslice, integral_indicator measurableSet_Iio]
    change (∫ r, _ ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Iio s))) = _
    rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, ← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    change ‖thetaCuspCenterTailWeight a r * g s‖ = thetaCuspCenterTailWeight a r * |g s|
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (thetaCuspCenterTailWeight_nonneg ha hr.1.le)]
  -- The triangle norm integral equals the weighted radial norm.
  have hInt : Integrable F (μ.prod μ) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hinner, ?_⟩
    apply hi.norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [hinner_norm, integral_apertureWeight_Ioo a hs.le, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg hs.le (Real.sinh_nonneg_iff.mpr (mul_nonneg ha hs.le)))]
  have houter_eq (r : ℝ) (hr : 0 < r) :
      (∫ s, F (s, r) ∂μ) = thetaCuspCenterTailWeight a r * (∫ s in Ioi r, g s) := by
    have hslice' : (fun s => F (s, r)) =
        (Ioi r).indicator (fun s => thetaCuspCenterTailWeight a r * g s) := rfl
    rw [hslice', integral_indicator measurableSet_Ioi]
    change (∫ s, _ ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi r))) = _
    rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi,
      max_eq_left hr.le, integral_const_mul]
  calc
    _ = ∫ r, ∫ s, F (s, r) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (houter_eq r hr).symm
    _ = ∫ s, ∫ r, F (s, r) ∂μ ∂μ := (integral_integral_swap (f := fun s r => F (s, r)) hInt).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [hinner_eq, integral_apertureWeight_Ioo a hs.le]


#print axioms integral_apertureWeight_mul_tail

end
end GaloisForLFunctions.CompletedArithmeticForms
