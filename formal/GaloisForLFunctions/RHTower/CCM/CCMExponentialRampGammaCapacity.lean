import GaloisForLFunctions.RHTower.CCM.CCMQuantileExponentialRampDeficit
import GaloisForLFunctions.RHTower.CCM.CCMCoherentSignedMomentGammaControl

/-!
# Finite Gamma capacity of the critical exponential ramp

The hyperbolic form of the reciprocal Gamma kernel supplies enough decay for
both exponential-ramp weights. Their joint capacity is at most five, uniformly
in the physical cutoff. No bound on the arithmetic transport fields is used.
-/

noncomputable section
open MeasureTheory Set Filter

namespace RHTower

theorem ccmGammaHigherBinetDualDensity_eq_sinh (r : ℝ) :
    ccmGammaHigherBinetDualDensity r = 2*Real.exp (3*r/2)*Real.sinh r := by
  symm
  rw [Real.sinh_eq]
  calc
    _ = Real.exp (3*r/2)*Real.exp r-Real.exp (3*r/2)*Real.exp (-r) := by ring
    _ = Real.exp (r/2)*Real.exp (2*r)-Real.exp (r/2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by unfold ccmGammaHigherBinetDualDensity; ring

/-- Hyperbolic positivity improves the exponential decay in the global singular-kernel bound. -/
theorem ccmGammaHigherBinetModeDensity_le_exp_threeHalf_div (r : {r : ℝ // 0 < r}) :
    ccmGammaHigherBinetModeDensity r ≤ Real.exp (-(3*(r : ℝ)/2))/(2*(r : ℝ)) := by
  have hk : 2*(r : ℝ)*Real.exp (3*(r : ℝ)/2) ≤ ccmGammaHigherBinetDualDensity r := by
    rw [ccmGammaHigherBinetDualDensity_eq_sinh]
    calc
      _ = 2*Real.exp (3*(r : ℝ)/2)*(r : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr r.2.le) (by positivity)
  calc
    _ ≤ 1/(2*(r : ℝ)*Real.exp (3*(r : ℝ)/2)) := by
      apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) r.2) (Real.exp_pos _))).mpr
      calc
        _ ≤ ccmGammaHigherBinetModeDensity r*ccmGammaHigherBinetDualDensity r :=
          mul_le_mul_of_nonneg_left hk (ccmGammaHigherBinetModeDensity_pos r.2).le
        _ = 1 := ccmGammaHigherBinetModeDensity_mul_dual r.2
    _ = _ := by rw [Real.exp_neg]; field_simp

private theorem abs_exp_sub_one_bound (x : ℝ) :
    |Real.exp x-1| ≤ |x| * Real.exp |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx))]
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    nlinarith only [h]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have h := Real.add_one_le_exp x
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hx')),
      abs_of_nonpos hx']
    calc
      _ ≤ -x := by linarith only [h]
      _ ≤ (-x)*Real.exp (-x) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.one_le_exp (neg_nonneg.mpr hx')) (neg_nonneg.mpr hx')

theorem abs_ccmExponentialRampDisplacementWeight_le (r : ℝ) :
    |ccmExponentialRampDisplacementWeight r| ≤ (|r|/2)*Real.exp (|r|/2) := by
  simpa only [ccmExponentialRampDisplacementWeight, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
    abs_exp_sub_one_bound (r/2)

theorem abs_ccmExponentialRampDerivativeWeight_le (r : ℝ) :
    |ccmExponentialRampDerivativeWeight r| ≤ |r| * Real.exp (|r|/2) := by
  rw [ccmExponentialRampDerivativeWeight, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (le_abs_self r) (by norm_num))) (abs_nonneg r)

def ccmExponentialRampGammaCapacityDensity (r : ℝ) : ℝ :=
  ((ccmExponentialRampDisplacementWeight r)^2+(ccmExponentialRampDerivativeWeight r)^2)*
    ccmGammaHigherBinetModeDensity |r|

theorem ccmExponentialRampGammaCapacityDensity_nonneg (r : ℝ) :
    0 ≤ ccmExponentialRampGammaCapacityDensity r :=
  mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (ccmGammaHigherBinetModeDensity_abs_nonneg r)

theorem ccmExponentialRampGammaCapacityDensity_le (r : ℝ) :
    ccmExponentialRampGammaCapacityDensity r ≤ (5/8 : ℝ)*|r| * Real.exp (-|r|/2) := by
  by_cases hr : r = 0
  · simp [hr, ccmExponentialRampGammaCapacityDensity, ccmExponentialRampDisplacementWeight,
      ccmExponentialRampDerivativeWeight]
  · have hR : 0 < |r| := abs_pos.mpr hr
    have ha := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
      (abs_ccmExponentialRampDisplacementWeight_le r)
    have hb := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
      (abs_ccmExponentialRampDerivativeWeight_le r)
    rw [sq_abs, mul_pow, div_pow] at ha
    rw [sq_abs, mul_pow] at hb
    have he : (Real.exp (|r|/2))^2 = Real.exp |r| := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he] at ha hb
    have hw : (ccmExponentialRampDisplacementWeight r)^2+(ccmExponentialRampDerivativeWeight r)^2 ≤
        (5/4 : ℝ)*|r|^2*Real.exp |r| := by nlinarith only [ha, hb]
    have hg := ccmGammaHigherBinetModeDensity_le_exp_threeHalf_div ⟨|r|, hR⟩
    calc
      _ ≤ ((5/4 : ℝ)*|r|^2*Real.exp |r|)*(Real.exp (-(3*|r|/2))/(2*|r|)) :=
        mul_le_mul hw hg (ccmGammaHigherBinetModeDensity_abs_nonneg r) (by positivity)
      _ = (5/8 : ℝ)*|r| * (Real.exp |r| * Real.exp (-(3*|r|/2))) := by field_simp; ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring

private theorem major_integrable_positive :
    IntegrableOn (fun r : ℝ => r*Real.exp (-r/2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
    (b := (1/2 : ℝ)) (by norm_num) le_rfl (by norm_num)
  simpa only [Real.rpow_one, neg_mul, one_div_mul_eq_div, neg_div] using h

private theorem major_integrable :
    Integrable (fun r : ℝ => |r| * Real.exp (-|r|/2)) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have hp : IntegrableOn (fun r : ℝ => |r| * Real.exp (-|r|/2)) (Ioi 0) :=
    major_integrable_positive.congr_fun (fun r hr => by rw [abs_of_pos hr]) measurableSet_Ioi
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

theorem integrable_ccmExponentialRampGammaCapacityDensity :
    Integrable ccmExponentialRampGammaCapacityDensity := by
  apply Integrable.mono' (major_integrable.const_mul (5/8 : ℝ))
  · apply Measurable.aestronglyMeasurable
    unfold ccmExponentialRampGammaCapacityDensity ccmExponentialRampDisplacementWeight
      ccmExponentialRampDerivativeWeight ccmGammaHigherBinetModeDensity
    fun_prop
  · filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (ccmExponentialRampGammaCapacityDensity_nonneg r)]
    simpa only [mul_assoc] using ccmExponentialRampGammaCapacityDensity_le r

def ccmExponentialRampGammaCapacity : ℝ := ∫ r : ℝ, ccmExponentialRampGammaCapacityDensity r

theorem ccmExponentialRampGammaCapacity_nonneg : 0 ≤ ccmExponentialRampGammaCapacity :=
  integral_nonneg ccmExponentialRampGammaCapacityDensity_nonneg

/-- The actual critical test has fixed capacity at most five. -/
theorem ccmExponentialRampGammaCapacity_le_five : ccmExponentialRampGammaCapacity ≤ 5 := by
  have hm : (∫ r : ℝ, |r| * Real.exp (-|r|/2)) = 8 := by
    rw [integral_comp_abs (f := fun r : ℝ => r*Real.exp (-r/2))]
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : ℝ)) (r := (1/2 : ℝ)) (by norm_num) (by norm_num)
    have hg : Real.Gamma 2 = 1 := by
      simpa only [Nat.cast_one, one_add_one_eq_two, Nat.factorial_one] using Real.Gamma_nat_eq_factorial 1
    norm_num [Real.rpow_two, hg] at h
    have h' : (∫ r : ℝ in Ioi 0, r*Real.exp (-r/2)) = 4 := by
      simpa only [neg_mul, one_div_mul_eq_div, neg_div] using h
    rw [h']
    norm_num
  have h := integral_mono integrable_ccmExponentialRampGammaCapacityDensity
    (major_integrable.const_mul (5/8 : ℝ))
    (fun r => by simpa only [mul_assoc] using ccmExponentialRampGammaCapacityDensity_le r)
  rw [integral_const_mul, hm] at h
  norm_num at h
  exact h

end RHTower
