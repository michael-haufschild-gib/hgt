import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairApertureRemainder
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerProductFiberNormalForm

/-!
# Ordinary-pair truncation of the Hedenmalm current

Integrating the aperture weight over a center triangle identifies the
aperture-weighted Fourier tail with half the actual Hedenmalm current.
The ordinary-pair remainder estimate therefore applies to that current
with its exact Fourier normalization.
-/

open MeasureTheory Set Complex Filter Topology
open scoped BigOperators
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

private theorem integral_weight_mul_tail {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ}
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
  -- The triangle norm integral equals the admitted weighted radial norm.
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

private theorem stronglyMeasurable_fullRadialWigner (b : ℝ) :
    StronglyMeasurable (fun s : ℝ =>
      (thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re) := by
  let K : ℝ × ℝ → ℂ := fun p =>
    thetaCuspComplexSource (p.1 / 2 + p.2) *
      (starRingEnd ℂ) (thetaCuspComplexSource (p.1 / 2 - p.2)) *
        thetaWignerDifferencePhase b p.2
  have hc : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hK : Continuous K := by
    unfold K thetaCuspComplexSource thetaWignerDifferencePhase
    fun_prop
  have hC := hK.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  simpa only [K, thetaWignerDistribution] using
    Complex.continuous_re.comp_stronglyMeasurable hC

private theorem integrableOn_fullWeightedRadialWigner {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    IntegrableOn (fun s : ℝ => (s * Real.sinh (a * s) : ℝ) *
      thetaWignerDistribution thetaCuspComplexSource (s / 2) b) (Ioi 0) := by
  have hi := (integrable_thetaWignerCenterMixKernel (b := b) ha0 ha).integral_prod_left
  apply hi.congr
  filter_upwards with s
  rw [thetaWignerDistribution, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [thetaWignerCenterMixKernel]
  ring

/-- Integrating the literal full-source tail against the aperture weight recovers the radial current. -/
theorem thetaFullApertureTail_eq_radialIntegral {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) (b : ℝ) :
    thetaFullApertureTail a b =
      ∫ s in Ioi (0 : ℝ), s * Real.sinh (a * s) *
        (thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re := by
  apply integral_weight_mul_tail ha0 (stronglyMeasurable_fullRadialWigner b)
  have h := Complex.reCLM.integrable_comp (integrableOn_fullWeightedRadialWigner ha0 ha b)
  change IntegrableOn (fun s : ℝ =>
    ((s * Real.sinh (a * s) : ℝ) *
      thetaWignerDistribution thetaCuspComplexSource (s / 2) b : ℂ).re) (Ioi 0) at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

/-- Exact normalization between the aperture-weighted Fourier tail and the Hedenmalm current. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_two_mul_apertureTail {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith) b =
      2 * thetaFullApertureTail a b := by
  rw [thetaCuspCenterMixedFourierCurrent_eq_two_mul_re_radialWigner ha0 ha b,
    thetaFullApertureTail_eq_radialIntegral ha0 ha b]
  congr 1
  have hre := Complex.reCLM.integral_comp_comm (integrableOn_fullWeightedRadialWigner ha0 ha b)
  change (∫ s in Ioi (0 : ℝ),
    ((s * Real.sinh (a * s) : ℝ) *
      thetaWignerDistribution thetaCuspComplexSource (s / 2) b : ℂ).re) =
    (∫ s in Ioi (0 : ℝ), (s * Real.sinh (a * s) : ℝ) *
      thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re at hre
  rw [← hre]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Ordinary ordered pairs approximate the actual Hedenmalm current uniformly in frequency. -/
theorem thetaCuspCenterMixedFourierCurrent_pair_remainder_le {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) (M : ℕ) :
    |thetaCuspCenterMixedFourierCurrent a (by rw [abs_of_nonneg ha0]; linarith) b -
      2 * ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
        thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b| ≤
      288 * a * besselFirstAtomTailCost 0 * Real.exp (-Real.pi * ((M : ℝ) + 1)) /
        ((9 - a ^ 2) ^ 2 * (1 - Real.exp (-Real.pi)) ^ 2) := by
  rw [thetaCuspCenterMixedFourierCurrent_eq_two_mul_apertureTail ha0 ha b,
    ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (144 * a * besselFirstAtomTailCost 0 * Real.exp (-Real.pi * ((M : ℝ) + 1)) /
        ((9 - a ^ 2) ^ 2 * (1 - Real.exp (-Real.pi)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (thetaFullApertureTail_remainder_le ha0 ha b M) (by norm_num)
    _ = _ := by ring

end
end GaloisForLFunctions.CompletedArithmeticForms
