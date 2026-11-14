import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderHasAnExactEnergyIdentity

/-!
# Positive Gamma remainder through lag radius two

Reciprocal hyperbolic bounds on the unit interval retain positive fourth-order
terms. The resulting cubic and quartic lag weights remain valid across the
prime-three and prime-four windows.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory BiScaleUncertainty SpacingScaleHarmonicAnalysis

private theorem reciprocal_hyperbolic_lower_unit {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1) :
    1 - z ^ 2 / 6 + z ^ 4 / 64 ≤ z / Real.sinh z ∧
      1 - z ^ 2 / 2 + z ^ 4 / 7 ≤ 1 / Real.cosh z := by
  have hz : |z| ≤ 1 := by rwa [abs_of_pos h0]
  have hzn : |-z| ≤ 1 := by rwa [abs_neg]
  have hp := exp_le_taylor_six hz
  have hm := exp_le_taylor_six hzn
  have hm' := taylor_six_le_exp hzn
  rw [abs_neg, abs_of_pos h0] at hm hm'
  rw [abs_of_pos h0] at hp
  have hS : Real.sinh z ≤ z + z ^ 3 / 6 + z ^ 5 / 120 + z ^ 6 / 617 := by
    rw [Real.sinh_eq]
    nlinarith only [hp, hm']
  have hC : Real.cosh z ≤ 1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 617 := by
    rw [Real.cosh_eq]
    nlinarith only [hp, hm]
  have hz2 : z ^ 2 ≤ 1 := by nlinarith only [h0, h1]
  have hz4 : z ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ (sq_nonneg z) hz2 2
    norm_num only [← pow_mul, one_pow] at h
    exact h
  have hz42 : z ^ 4 ≤ z ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hz2 (sq_nonneg z)
    nlinarith only [h]
  have hA0 : 0 ≤ 1 - z ^ 2 / 6 + z ^ 4 / 64 := by
    nlinarith only [hz2, sq_nonneg (z ^ 2)]
  have hA1 : 1 - z ^ 2 / 6 + z ^ 4 / 64 ≤ 1 := by
    nlinarith only [hz42, sq_nonneg z]
  have hB0 : 0 ≤ 1 - z ^ 2 / 2 + z ^ 4 / 7 := by
    nlinarith only [hz2, sq_nonneg (z ^ 2)]
  have hB1 : 1 - z ^ 2 / 2 + z ^ 4 / 7 ≤ 1 := by
    nlinarith only [hz42, sq_nonneg z]
  constructor
  · apply (le_div_iff₀ (Real.sinh_pos_iff.mpr h0)).mpr
    have hs := mul_le_mul_of_nonneg_left hS hA0
    have hr := mul_le_mul_of_nonneg_right hA1 (show 0 ≤ z ^ 6 / 617 by positivity)
    have hpoly : (1 - z ^ 2 / 6 + z ^ 4 / 64) * (z + z ^ 3 / 6 + z ^ 5 / 120) +
        z ^ 6 / 617 ≤ z := by
      have he : (1 - z ^ 2 / 6 + z ^ 4 / 64) * (z + z ^ 3 / 6 + z ^ 5 / 120) +
          z ^ 6 / 617 - z = z ^ 5 * (-11 / 2880 + z / 617 + 7 * z ^ 2 / 5760 + z ^ 4 / 7680) := by
        ring
      have hb : -11 / 2880 + z / 617 + 7 * z ^ 2 / 5760 + z ^ 4 / 7680 ≤ (0 : ℝ) := by
        linarith only [h1, hz2, hz4]
      have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z ^ 5 by positivity) hb
      rw [← he] at hn
      linarith only [hn]
    nlinarith only [hs, hr, hpoly]
  · apply (le_div_iff₀ (Real.cosh_pos z)).mpr
    have hc := mul_le_mul_of_nonneg_left hC hB0
    have hr := mul_le_mul_of_nonneg_right hB1 (show 0 ≤ z ^ 6 / 617 by positivity)
    have hpoly : (1 - z ^ 2 / 2 + z ^ 4 / 7) * (1 + z ^ 2 / 2 + z ^ 4 / 24) +
        z ^ 6 / 617 ≤ (1 : ℝ) := by
      have he : (1 - z ^ 2 / 2 + z ^ 4 / 7) * (1 + z ^ 2 / 2 + z ^ 4 / 24) +
          z ^ 6 / 617 - 1 = z ^ 4 * (-11 / 168 + 17 * z ^ 2 / 336 + z ^ 4 / 168 + z ^ 2 / 617) := by
        ring
      have hb : -11 / 168 + 17 * z ^ 2 / 336 + z ^ 4 / 168 + z ^ 2 / 617 ≤ (0 : ℝ) := by
        linarith only [hz2, hz4]
      have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z ^ 4 by positivity) hb
      rw [← he] at hn
      linarith only [hn]
    nlinarith only [hc, hr, hpoly]

/-- The cubic and quartic Gamma reserves persist through lag radius two. -/
theorem retainedGammaRemainderWeight_ge_higher_lags_to_two {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 2) :
    t ^ 3 / 1024 + t ^ 4 / 224 ≤ retainedGammaRemainderWeight t := by
  obtain ⟨hs, hc⟩ := reciprocal_hyperbolic_lower_unit
    (z := t / 2) (by linarith only [ht.1]) (by linarith only [ht.2])
  have hden : Real.sinh (t / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by linarith only [ht.1])).ne'
  have he : archLevySinhWeight t =
      1 / (2 * Real.sinh (t / 2)) + 1 / (2 * Real.cosh (t / 2)) := by
    rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1,
      archLevyDensity_eq_inv_sinh_add_inv_cosh ht.1]
    ring
  have hm := mul_le_mul_of_nonneg_left hs (le_of_lt (one_div_pos.mpr ht.1))
  have heq : 1 / t * ((t / 2) / Real.sinh (t / 2)) = 1 / (2 * Real.sinh (t / 2)) := by
    field_simp [ht.1.ne', hden]
  rw [heq] at hm
  unfold retainedGammaRemainderWeight
  rw [he]
  have hp : 1 / t * (1 - (t / 2) ^ 2 / 6 + (t / 2) ^ 4 / 64) +
      (1 - (t / 2) ^ 2 / 2 + (t / 2) ^ 4 / 7) / 2 =
      1 / t + 1 / 2 - t / 24 - t ^ 2 / 16 + t ^ 3 / 1024 + t ^ 4 / 224 := by
    field_simp [ht.1.ne']
    ring
  have hcHalf := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcEq : (1 / 2 : ℝ) * (1 / Real.cosh (t / 2)) = 1 / (2 * Real.cosh (t / 2)) := by ring
  rw [hcEq] at hcHalf
  linarith only [hm, hcHalf, hp]

/-- Both pieces of the logarithmic Gamma decomposition are integrable through radius two. -/
theorem local_gamma_terms_integrable_to_two {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) :
    IntegrableOn (fun t => (autocorr F 0 - autocorr F t) / t) (Ioc (0 : ℝ) 2) ∧
    IntegrableOn (fun t => retainedGammaRemainderWeight t *
      (autocorr F 0 - autocorr F t)) (Ioc (0 : ℝ) 2) := by
  let D := fun t => autocorr F 0 - autocorr F t
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hdc : Continuous D := continuous_const.sub hc
  have hd (t : ℝ) : 0 ≤ D t := sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hi : IntegrableOn (fun t => D t * archLevySinhWeight t) (Ioi (0 : ℝ)) :=
    integrableOn_biScaleLevyIntegrand hF hcs
  have hsub : Ioc (0 : ℝ) 2 ⊆ Ioi 0 := fun _ ht => ht.1
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) 2) := by
    apply (hi.mono_set hsub).mono'
      ((hdc.measurable.div measurable_id).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖D t / t‖ ≤ D t * archLevySinhWeight t
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hd t) ht.1.le)]
    have hr := retainedGammaRemainderWeight_ge_higher_lags_to_two ht
    have ht2 : t ^ 2 ≤ 4 := by nlinarith only [ht.1, ht.2]
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.1.le 3
    have ht4 : 0 ≤ t ^ 4 := pow_nonneg ht.1.le 4
    have hwinv : 1 / t ≤ archLevySinhWeight t := by
      unfold retainedGammaRemainderWeight at hr
      linarith only [hr, ht.2, ht2, ht3, ht4]
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hwinv (hd t)
  have hiD : IntegrableOn D (Ioc (0 : ℝ) 2) :=
    hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hitD : IntegrableOn (fun t => t * D t) (Ioc (0 : ℝ) 2) :=
    (continuous_id.mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hit2D : IntegrableOn (fun t => t ^ 2 * D t) (Ioc (0 : ℝ) 2) :=
    ((continuous_pow 2).mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨hilog, ?_⟩
  apply (((((hi.mono_set hsub).sub hilog).sub (hiD.div_const 2)).add
    (hitD.div_const 24)).add (hit2D.div_const 16)).congr
  exact Eventually.of_forall fun t => by dsimp [retainedGammaRemainderWeight, D]; ring

#print axioms retainedGammaRemainderWeight_ge_higher_lags_to_two
#print axioms local_gamma_terms_integrable_to_two

end GaloisForLFunctions.WindowTowerOfSpecZ
