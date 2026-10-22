import GaloisForLFunctions.RHTower.CCM.CCMCoherentSignedMomentCharge
import GaloisForLFunctions.RHTower.CCM.CCMGammaFractionalDensity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Gamma control of the literal arithmetic moment charge

The second displacement moment of the higher-Binet kernel has finite capacity,
uniformly bounded by eight. Completing a weighted square gives the exact
dual-action inequality and hence a square-root energy bound for the signed
charge and for completed characteristic curvature. The arithmetic energy is
the literal prime-plus-terminal energy; its cutoff growth is not assumed.
-/

noncomputable section
open MeasureTheory Set Filter

namespace RHTower

theorem ccmGammaHigherBinetModeDensity_abs_nonneg (r : ℝ) :
    0 ≤ ccmGammaHigherBinetModeDensity |r| := by
  by_cases hr : r = 0
  · simp [hr, ccmGammaHigherBinetModeDensity]
  · exact (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)).le

private theorem density_bound {r : ℝ} (hr : 0 < r) :
    r^2*ccmGammaHigherBinetModeDensity r ≤ r*Real.exp (-(1/2 : ℝ)*r) := by
  calc
    _ ≤ r^2*(Real.exp (-r/2)/r) := mul_le_mul_of_nonneg_left
      (ccmGammaHigherBinetModeDensity_le_exp_div ⟨r, hr⟩) (sq_nonneg r)
    _ = _ := by
      rw [show -r/2 = -(1/2 : ℝ)*r by ring]
      field_simp

private theorem major_integrable :
    IntegrableOn (fun r : ℝ => r*Real.exp (-(1/2 : ℝ)*r)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (b := (1/2 : ℝ)) (by norm_num) le_rfl (by norm_num))

/-- The displacement factor removes the kernel singularity at zero. -/
theorem ccmGammaSignedMomentCapacityDensity_le_abs (r : ℝ) :
    r^2*ccmGammaHigherBinetModeDensity |r| ≤ |r| := by
  by_cases hr : r = 0
  · simp [hr]
  · have h := density_bound (abs_pos.mpr hr)
    rw [sq_abs] at h
    have he : Real.exp (-(1/2 : ℝ)*|r|) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (abs_nonneg r))
    exact h.trans ((mul_le_mul_of_nonneg_left he (abs_nonneg r)).trans_eq (mul_one _))

private theorem density_integrableOn :
    IntegrableOn (fun r : ℝ => r^2*ccmGammaHigherBinetModeDensity r) (Ioi 0) := by
  apply Integrable.mono' major_integrable
  · apply Measurable.aestronglyMeasurable
    unfold ccmGammaHigherBinetModeDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg r) (ccmGammaHigherBinetModeDensity_pos hr).le)]
    exact density_bound hr

theorem integrable_ccmGammaSignedMomentCapacityDensity :
    Integrable (fun r : ℝ => r^2*ccmGammaHigherBinetModeDensity |r|) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have hp : IntegrableOn (fun r : ℝ => r^2*ccmGammaHigherBinetModeDensity |r|) (Ioi 0) :=
    density_integrableOn.congr_fun (fun r hr => by rw [abs_of_pos hr]) measurableSet_Ioi
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, neg_sq, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

def ccmGammaSignedMomentCapacity : ℝ :=
  ∫ r : ℝ, r^2*ccmGammaHigherBinetModeDensity |r|

theorem ccmGammaSignedMomentCapacity_pos : 0 < ccmGammaSignedMomentCapacity := by
  apply (integral_pos_iff_support_of_nonneg
    (fun r => mul_nonneg (sq_nonneg r) (ccmGammaHigherBinetModeDensity_abs_nonneg r))
    integrable_ccmGammaSignedMomentCapacityDensity).mpr
  apply lt_of_lt_of_le (by norm_num : 0 < volume (Ioc (1 : ℝ) 2))
    (measure_mono ?_)
  intro r hr
  have hr0 : 0 < r := lt_trans (by norm_num) hr.1
  exact ne_of_gt (mul_pos (sq_pos_of_pos hr0)
    (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr (ne_of_gt hr0))))

/-- A fixed numerical capacity, independent of aperture and prime cutoff. -/
theorem ccmGammaSignedMomentCapacity_le_eight : ccmGammaSignedMomentCapacity ≤ 8 := by
  have hm : (∫ r : ℝ in Ioi 0, r*Real.exp (-(1/2 : ℝ)*r)) = 4 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : ℝ)) (r := (1/2 : ℝ)) (by norm_num) (by norm_num)
    have hg : Real.Gamma 2 = 1 := by
      simpa only [Nat.cast_one, one_add_one_eq_two, Nat.factorial_one] using Real.Gamma_nat_eq_factorial 1
    norm_num [Real.rpow_two, hg] at h
    simpa only [neg_mul] using h
  calc
    ccmGammaSignedMomentCapacity = 2*(∫ r : ℝ in Ioi 0,
        r^2*ccmGammaHigherBinetModeDensity r) := by
      calc
        _ = ∫ r : ℝ, |r|^2*ccmGammaHigherBinetModeDensity |r| := by
          apply integral_congr_ae
          filter_upwards with r
          rw [sq_abs]
        _ = _ := integral_comp_abs (f := fun r : ℝ => r^2*ccmGammaHigherBinetModeDensity r)
    _ ≤ 2*(∫ r : ℝ in Ioi 0, r*Real.exp (-(1/2 : ℝ)*r)) := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact setIntegral_mono_on density_integrableOn major_integrable measurableSet_Ioi
        (fun r hr => density_bound hr)
    _ = 8 := by rw [hm]; ring

theorem ccmGammaSignedMomentWeightedSquare (r m t : ℝ) :
    (m*Real.sqrt (ccmGammaHigherBinetDualDensity |r|) -
      t*r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|))^2 =
      m^2*ccmGammaHigherBinetDualDensity |r| - 2*t*(r*m) +
        t^2*(r^2*ccmGammaHigherBinetModeDensity |r|) := by
  by_cases hr : r = 0
  · simp [hr, ccmGammaHigherBinetDualDensity, ccmGammaHigherBinetModeDensity]
  · have hk := ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
    have hg := ccmGammaHigherBinetModeDensity_abs_nonneg r
    have hs : Real.sqrt (ccmGammaHigherBinetDualDensity |r|) *
        Real.sqrt (ccmGammaHigherBinetModeDensity |r|) = 1 := by
      rw [← Real.sqrt_mul hk, mul_comm, ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr),
        Real.sqrt_one]
    calc
      _ = m^2*(Real.sqrt (ccmGammaHigherBinetDualDensity |r|))^2 -
          2*t*(r*m)*(Real.sqrt (ccmGammaHigherBinetDualDensity |r|)*
            Real.sqrt (ccmGammaHigherBinetModeDensity |r|)) +
          t^2*r^2*(Real.sqrt (ccmGammaHigherBinetModeDensity |r|))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hk, Real.sq_sqrt hg, hs]; ring

/-- Completing the reciprocal-Gamma square bounds every dual action parameter. -/
theorem ccmActualHeadSignedMomentCharge_dual_bound (T : ℝ) (N : ℕ) (t : ℝ) :
    2*t*ccmActualHeadSignedMomentCharge T N ≤
      ccmActualHeadSignedMomentGammaEnergy T N + t^2*ccmGammaSignedMomentCapacity := by
  have hpoint (r : ℝ) : 2*t*(r*ccmActualHeadMidpointSignedMoment T N r) ≤
      (ccmActualHeadMidpointSignedMoment T N r)^2*ccmGammaHigherBinetDualDensity |r| +
        t^2*(r^2*ccmGammaHigherBinetModeDensity |r|) := by
    have h := sq_nonneg (ccmActualHeadMidpointSignedMoment T N r *
      Real.sqrt (ccmGammaHigherBinetDualDensity |r|) -
      t*r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|))
    rw [ccmGammaSignedMomentWeightedSquare] at h
    linarith only [h]
  have h := integral_mono ((integrable_ccmActualHeadSignedMoment_displacement T N).const_mul (2*t))
    ((integrable_ccmActualHeadSignedMomentGammaDensity T N).add
      (integrable_ccmGammaSignedMomentCapacityDensity.const_mul (t^2))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_ccmActualHeadSignedMomentGammaDensity T N)
    (integrable_ccmGammaSignedMomentCapacityDensity.const_mul (t^2))] at h
  simpa only [integral_const_mul, ccmActualHeadSignedMomentCharge,
    ccmActualHeadSignedMomentGammaEnergy, ccmGammaSignedMomentCapacity] using h

/-- The exact kernel capacity controls the signed arithmetic charge. -/
theorem sq_ccmActualHeadSignedMomentCharge_le_capacity (T : ℝ) (N : ℕ) :
    (ccmActualHeadSignedMomentCharge T N)^2 ≤
      ccmGammaSignedMomentCapacity*ccmActualHeadSignedMomentGammaEnergy T N := by
  have h := ccmActualHeadSignedMomentCharge_dual_bound T N
    (ccmActualHeadSignedMomentCharge T N/ccmGammaSignedMomentCapacity)
  have he : (ccmActualHeadSignedMomentCharge T N/ccmGammaSignedMomentCapacity)^2 *
      ccmGammaSignedMomentCapacity = (ccmActualHeadSignedMomentCharge T N)^2/
        ccmGammaSignedMomentCapacity := by field_simp [ne_of_gt ccmGammaSignedMomentCapacity_pos]
  rw [he] at h
  have hl : 2*(ccmActualHeadSignedMomentCharge T N/ccmGammaSignedMomentCapacity)*
      ccmActualHeadSignedMomentCharge T N =
      2*((ccmActualHeadSignedMomentCharge T N)^2/ccmGammaSignedMomentCapacity) := by ring
  rw [hl] at h
  have hd : (ccmActualHeadSignedMomentCharge T N)^2/ccmGammaSignedMomentCapacity ≤
      ccmActualHeadSignedMomentGammaEnergy T N := by linarith only [h]
  simpa only [mul_comm] using (div_le_iff₀ ccmGammaSignedMomentCapacity_pos).mp hd

theorem sq_ccmActualHeadSignedMomentCharge_le_eight_energy (T : ℝ) (N : ℕ) :
    (ccmActualHeadSignedMomentCharge T N)^2 ≤ 8*ccmActualHeadSignedMomentGammaEnergy T N :=
  (sq_ccmActualHeadSignedMomentCharge_le_capacity T N).trans
    (mul_le_mul_of_nonneg_right ccmGammaSignedMomentCapacity_le_eight
      (ccmActualHeadSignedMomentGammaEnergy_nonneg T N))

/-- Completed prime--polar curvature is controlled by actual arithmetic Gamma energy. -/
theorem sq_ccmActualHeadCompletedCosineCurvature_le_gammaEnergy (T : ℝ) (N : ℕ) :
    (deriv (deriv (ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T)) 0)^2 ≤
      128*Real.pi^2*ccmActualHeadSignedMomentGammaEnergy T N := by
  rw [ccmActualHeadCompletedCosineCurvature_eq_signedMomentCharge]
  nlinarith [mul_le_mul_of_nonneg_left (sq_ccmActualHeadSignedMomentCharge_le_eight_energy T N)
    (sq_nonneg (4*Real.pi))]

end RHTower
