import GaloisForLFunctions.RHTower.PaperThetaPairedCdf
import GaloisForLFunctions.RHTower.PaperThetaL1Domain
import GaloisForLFunctions.RHTower.ThetaQuantileKronReduction
import GaloisForLFunctions.RHTower.HedenmalmQuantileSliceMoment

/-! # Paid paired Dini cancellation at the divisor seam -/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry FourierLLogL

def seamDini (z : ℂ) (t : ℝ) : ℂ :=
  (periodicMode z t + periodicMode z (-t) + 2) / (Real.sin (Real.pi*t) : ℂ)

theorem measurable_seamDini (z : ℂ) : Measurable (seamDini z) :=
  (((measurable_periodicMode z).add ((measurable_periodicMode z).comp measurable_neg)).add
    measurable_const).div
      (Complex.continuous_ofReal.measurable.comp ((measurable_const.mul measurable_id).sin))

/-- On the divisor, the two sides of the seam are the opposite-parameter pair at one end. -/
theorem seam_pair_eq_upper_pair (z : {z : ℂ // XiC z = 0}) (t : Ioo (0 : ℝ) 1) :
    periodicMode z.val t.val + periodicMode z.val (-t.val) + 2 =
      flatModePullback z.val (1-t.val) + flatModePullback (-z.val) (1-t.val) + 2 := by
  have ht : 1-t.val ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
  have hp : periodicMode z.val (-t.val) = periodicMode z.val (1-t.val) := by
    have h := periodic_periodicMode z.val (-t.val)
    simpa only [show -t.val+1 = 1-t.val by ring] using h.symm
  rw [hp, periodicMode_eq_pullback z.val t, periodicMode_eq_pullback z.val ⟨1-t.val, ht⟩]
  have hr : flatModePullback z.val t.val = flatModePullback (-z.val) (1-t.val) := by
    rw [flatModePullback_eq_flatQuotient, flatModePullback_eq_flatQuotient,
      quantileFun_one_sub t.2]
    exact flatQuotient_divisor_reflection z _
  rw [hr, add_comm (flatModePullback (-z.val) (1-t.val))]

private theorem upper_pair_integrable (z : ℂ) :
    IntegrableOn (fun t : ℝ =>
      (flatModePullback z t+flatModePullback (-z) t+2)/((1-t : ℝ) : ℂ))
        (Icc (1/2 : ℝ) 1) := by
  have h := integrable_upper_pair_div_tail z
  rw [cdfFun_thetaSource_zero, unitIntervalMeasure, integrable_indicator_iff measurableSet_Ici,
    IntegrableOn, Measure.restrict_restrict measurableSet_Ici] at h
  change IntegrableOn _ (Ici (1/2 : ℝ) ∩ Icc 0 1) at h
  apply h.mono_set
  intro t ht
  exact ⟨ht.1, by linarith [ht.1], ht.2⟩

private theorem reflected_pair_integrable (z : ℂ) :
    IntegrableOn (fun t : ℝ =>
      (flatModePullback z (1-t)+flatModePullback (-z) (1-t)+2)/(t : ℂ))
        (Ioo (0 : ℝ) (1/2)) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)).mpr
    (upper_pair_integrable z)
  have hr := (hi.comp_sub_left 1).symm
  norm_num only [sub_self, show (1 : ℝ)-1/2=1/2 by ring, sub_sub_cancel] at hr
  have hs := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)).mp hr
  exact hs.mono_set Ioo_subset_Icc_self

/-- The actual paired sine quotient is integrable; no endpoint regularity premise remains. -/
theorem integrableOn_seamDini (z : {z : ℂ // XiC z = 0}) :
    IntegrableOn (seamDini z.val) (Ico (0 : ℝ) (1/2)) := by
  apply (integrableOn_Ico_iff_integrableOn_Ioo (by finiteness)).mpr
  apply ((reflected_pair_integrable z.val).norm.const_mul (2/Real.pi)).mono'
    (measurable_seamDini z.val).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := by linarith [ht.2]
  have hs : Real.pi*t/2 ≤ |Real.sin (Real.pi*t)| := by
    have harg : |Real.pi*t| ≤ Real.pi/2 := by
      rw [abs_of_pos (mul_pos Real.pi_pos ht0)]
      nlinarith [Real.pi_pos, ht.2]
    simpa only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos ht0]
      using Period.sin_posabs harg
  have hnum := seam_pair_eq_upper_pair z ⟨t, ht0, ht1⟩
  rw [seamDini, hnum, norm_div, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖flatModePullback z.val (1-t)+flatModePullback (-z.val) (1-t)+2‖ /
        (Real.pi*t/2) := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hs
    _ = _ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      ring

end RHTower.PaperThetaEndpoint
