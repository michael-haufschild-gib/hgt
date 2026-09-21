import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianCertificatePhaseFlipPrimeGrowth

/-!
# Explicit digamma payment at the Gaussian phase flip

The Gaussian certificate peak obstruction leaves two possible payment
channels: a digamma gain and retained prime-power oscillation.  This module
bounds the first channel directly from the exact digamma transform.  Splitting
at `u = 1` gives an explicit elementary majorant, so any certificate whose
compact interval reaches `π / ε` must pay the remaining phase-flip peak with
its retained logarithmic prime slope mass.
-/

open Filter MeasureTheory Topology Set

namespace RiemannGaussian
noncomputable section

private def gaussianDigammaPhaseFlipIntegrand (ε : ℝ) (u : ℝ) : ℝ :=
  gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u *
    Real.exp (-u ^ 2 / (4 * ε))

private theorem gaussianDigammaPhaseFlipIntegrand_nonnegative
    {ε : ℝ} {u : ℝ} (hu : 0 < u) :
    0 ≤ gaussianDigammaPhaseFlipIntegrand ε u := by
  unfold gaussianDigammaPhaseFlipIntegrand gaussianSuzukiDigammaOscillationIntegrand
    gaussianSuzukiDigammaDensity
  have hden : 0 < 1 - Real.exp (-2 * u) := by
    simpa only [neg_mul] using
      GaloisForLFunctions.RHTower.one_sub_exp_neg_two_mul_pos hu
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg (Real.exp_pos _).le hden.le)
      (sub_nonneg.mpr (Real.cos_le_one _))
  · exact (Real.exp_pos _).le

private theorem gaussianDigammaPhaseFlipGaussian_le_one
    {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    Real.exp (-u ^ 2 / (4 * ε)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have hden : 0 ≤ 4 * ε := mul_nonneg (by norm_num) hε.le
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg u)) hden

private theorem integrableOn_gaussianDigammaPhaseFlipIntegrand_Ioc
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (gaussianDigammaPhaseFlipIntegrand ε) (Set.Ioc (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top
  · change AEStronglyMeasurable
        (gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) *
          fun u => Real.exp (-u ^ 2 / (4 * ε)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1))
    exact (((continuousOn_gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε)).mono
      Set.Ioc_subset_Ioi_self).mul
        (Real.continuous_exp.comp_continuousOn'
          ((continuous_id.pow 2).neg.continuousOn.div_const (4 * ε)))).aestronglyMeasurable
            measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    unfold gaussianDigammaPhaseFlipIntegrand
    have heq : ‖Real.exp (-u ^ 2 / (4 * ε))‖ =
        Real.exp (-u ^ 2 / (4 * ε)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, heq]
    calc
      ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ *
          Real.exp (-u ^ 2 / (4 * ε)) ≤
        ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ * 1 := by
          gcongr
          exact gaussianDigammaPhaseFlipGaussian_le_one hε u
      _ ≤ (3 / 2 : ℝ) * |Real.pi / ε| := by
        simpa only [mul_one] using
          norm_gaussianSuzukiDigammaOscillationIntegrand_le_near_zero
            (Real.pi / ε) hu.1 hu.2

private theorem integrableOn_gaussianDigammaPhaseFlipIntegrand_Ioi_one
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (gaussianDigammaPhaseFlipIntegrand ε) (Set.Ioi (1 : ℝ)) := by
  let C : ℝ := 2 / (1 - Real.exp (-2))
  have hmajor : IntegrableOn
      (fun u : ℝ => C * Real.exp (-(1 / 2 : ℝ) * u))
      (Set.Ioi (1 : ℝ)) := by
    exact (exp_neg_integrableOn_Ioi 1
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  apply hmajor.mono'
  · change AEStronglyMeasurable
        (gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) *
          fun u => Real.exp (-u ^ 2 / (4 * ε)))
        (volume.restrict (Set.Ioi (1 : ℝ)))
    exact (((continuousOn_gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε)).mono (by
      intro u hu
      change 1 < u at hu
      exact zero_lt_one.trans hu)).mul
        (Real.continuous_exp.comp_continuousOn'
          ((continuous_id.pow 2).neg.continuousOn.div_const (4 * ε)))).aestronglyMeasurable
            measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 1 < u at hu
    unfold gaussianDigammaPhaseFlipIntegrand
    have heq : ‖Real.exp (-u ^ 2 / (4 * ε))‖ =
        Real.exp (-u ^ 2 / (4 * ε)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, heq]
    calc
      ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ *
          Real.exp (-u ^ 2 / (4 * ε)) ≤
        ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ * 1 := by
          gcongr
          exact gaussianDigammaPhaseFlipGaussian_le_one hε u
      _ = ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ := by rw [mul_one]
      _ ≤ C * Real.exp (-(1 / 2 : ℝ) * u) :=
        norm_gaussianSuzukiDigammaOscillationIntegrand_le_tail _ hu.le

private theorem gaussianDigammaPhaseFlipIntegrand_near_le
    {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    gaussianDigammaPhaseFlipIntegrand ε u ≤
      (3 / 2 : ℝ) * |Real.pi / ε| := by
  have hnorm : ‖gaussianDigammaPhaseFlipIntegrand ε u‖ ≤
      (3 / 2 : ℝ) * |Real.pi / ε| := by
    unfold gaussianDigammaPhaseFlipIntegrand
    have heq : ‖Real.exp (-u ^ 2 / (4 * ε))‖ =
        Real.exp (-u ^ 2 / (4 * ε)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, heq]
    calc
      ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ *
          Real.exp (-u ^ 2 / (4 * ε)) ≤
        ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ * 1 := by
          gcongr
          exact gaussianDigammaPhaseFlipGaussian_le_one hε u
      _ ≤ (3 / 2 : ℝ) * |Real.pi / ε| := by
        simpa only [mul_one] using
          norm_gaussianSuzukiDigammaOscillationIntegrand_le_near_zero
            (Real.pi / ε) hu.1 hu.2
  rw [Real.norm_eq_abs, abs_of_nonneg
    (gaussianDigammaPhaseFlipIntegrand_nonnegative (ε := ε) hu.1)] at hnorm
  exact hnorm

private theorem gaussianDigammaPhaseFlipIntegrand_tail_le
    {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : u ∈ Set.Ioi (1 : ℝ)) :
    gaussianDigammaPhaseFlipIntegrand ε u ≤
      (2 / (1 - Real.exp (-2))) * Real.exp (-(1 / 2 : ℝ) * u) := by
  have hnorm : ‖gaussianDigammaPhaseFlipIntegrand ε u‖ ≤
      (2 / (1 - Real.exp (-2))) * Real.exp (-(1 / 2 : ℝ) * u) := by
    unfold gaussianDigammaPhaseFlipIntegrand
    have heq : ‖Real.exp (-u ^ 2 / (4 * ε))‖ =
        Real.exp (-u ^ 2 / (4 * ε)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, heq]
    calc
      ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ *
          Real.exp (-u ^ 2 / (4 * ε)) ≤
        ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ * 1 := by
          gcongr
          exact gaussianDigammaPhaseFlipGaussian_le_one hε u
      _ = ‖gaussianSuzukiDigammaOscillationIntegrand (Real.pi / ε) u‖ := by rw [mul_one]
      _ ≤ (2 / (1 - Real.exp (-2))) * Real.exp (-(1 / 2 : ℝ) * u) :=
        norm_gaussianSuzukiDigammaOscillationIntegrand_le_tail _ hu.le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (gaussianDigammaPhaseFlipIntegrand_nonnegative (ε := ε) (zero_lt_one.trans hu))] at hnorm
  exact hnorm

theorem gaussianDigammaGain_phaseFlip_le_explicit
    {ε : ℝ} (hε : 0 < ε) :
    gaussianDigammaGain ε (Real.pi / ε) ≤
      2 / Real.sqrt (Real.pi * ε) *
        ((3 / 2 : ℝ) * |Real.pi / ε| +
          (2 / (1 - Real.exp (-2))) * (2 * Real.exp (-(1 / 2 : ℝ)))) := by
  have hnear := integrableOn_gaussianDigammaPhaseFlipIntegrand_Ioc hε
  have htail := integrableOn_gaussianDigammaPhaseFlipIntegrand_Ioi_one hε
  have hsplit : (∫ u in Set.Ioi (0 : ℝ), gaussianDigammaPhaseFlipIntegrand ε u) =
      (∫ u in Set.Ioc (0 : ℝ) 1, gaussianDigammaPhaseFlipIntegrand ε u) +
        ∫ u in Set.Ioi (1 : ℝ), gaussianDigammaPhaseFlipIntegrand ε u := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hnear htail,
      Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hnearBound :
      (∫ u in Set.Ioc (0 : ℝ) 1, gaussianDigammaPhaseFlipIntegrand ε u) ≤
        (3 / 2 : ℝ) * |Real.pi / ε| := by
    calc
      (∫ u in Set.Ioc (0 : ℝ) 1, gaussianDigammaPhaseFlipIntegrand ε u) ≤
        ∫ _u in Set.Ioc (0 : ℝ) 1, (3 / 2 : ℝ) * |Real.pi / ε| :=
          setIntegral_mono_on hnear
            (integrableOn_const (C := (3 / 2 : ℝ) * |Real.pi / ε|)
              (hs := measure_Ioc_lt_top.ne))
            measurableSet_Ioc (fun u hu => gaussianDigammaPhaseFlipIntegrand_near_le hε hu)
      _ = (3 / 2 : ℝ) * |Real.pi / ε| := by
        have hvol : volume.real (Set.Ioc (0 : ℝ) 1) = 1 := by
          norm_num [Measure.real, Real.volume_Ioc]
        rw [setIntegral_const, hvol, smul_eq_mul, one_mul]
  let C : ℝ := 2 / (1 - Real.exp (-2))
  have htailBound :
      (∫ u in Set.Ioi (1 : ℝ), gaussianDigammaPhaseFlipIntegrand ε u) ≤
        C * (2 * Real.exp (-(1 / 2 : ℝ))) := by
    calc
      (∫ u in Set.Ioi (1 : ℝ), gaussianDigammaPhaseFlipIntegrand ε u) ≤
        ∫ u in Set.Ioi (1 : ℝ), C * Real.exp (-(1 / 2 : ℝ) * u) :=
          setIntegral_mono_on htail
            ((exp_neg_integrableOn_Ioi 1
              (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C)
            measurableSet_Ioi (fun u hu => by
              change 1 < u at hu
              simpa only [C] using gaussianDigammaPhaseFlipIntegrand_tail_le hε hu)
      _ = C * (2 * Real.exp (-(1 / 2 : ℝ))) := by
        rw [integral_const_mul,
          integral_exp_mul_Ioi (by norm_num : (-(1 / 2 : ℝ)) < 0) 1]
        ring_nf
  rw [gaussianDigammaGain_eq_gaussianSuzukiDigammaEnergy
    quarterLineDigammaGaussDifferenceFormula hε]
  have hintegral :
      (∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaDensity u *
          Real.exp (-u ^ 2 / (4 * ε)) *
            (1 - Real.cos ((Real.pi / ε) * u))) =
        ∫ u in Set.Ioi (0 : ℝ), gaussianDigammaPhaseFlipIntegrand ε u := by
    apply integral_congr_ae
    filter_upwards with u
    unfold gaussianDigammaPhaseFlipIntegrand gaussianSuzukiDigammaOscillationIntegrand
    ring_nf
  rw [hintegral, hsplit]
  dsimp only [C] at htailBound
  have hfactor : 0 ≤ 2 / Real.sqrt (Real.pi * ε) := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add hnearBound htailBound) hfactor


/-- If the compact part of a Gaussian arithmetic certificate reaches the phase
flip, its retained logarithmic prime slope mass must pay the elementary peak
remaining after the explicit digamma estimate. -/
theorem GaussianArithmeticWidthCertificate.phaseFlipPeak_sub_explicitDigamma_le_slopeMass
    {ε : ℝ} (certificate : GaussianArithmeticWidthCertificate ε)
    (hphaseRadius : Real.pi / ε ≤ certificate.compactRadius) :
    4 * Real.exp (ε / 4) +
        4 * Real.exp (ε / 4 - Real.pi ^ 2 / ε) -
      2 / Real.sqrt (Real.pi * ε) *
        ((3 / 2 : ℝ) * |Real.pi / ε| +
          (2 / (1 - Real.exp (-2))) * (2 * Real.exp (-(1 / 2 : ℝ)))) ≤
      2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
        gaussianPrimePhaseSlopeMass (Finset.range certificate.cutoff) := by
  have hpayment := certificate.phaseFlipPeak_le_digammaGain_add_slopeMass hphaseRadius
  have hdigest := gaussianDigammaGain_phaseFlip_le_explicit certificate.width_pos
  linarith

end
end RiemannGaussian
