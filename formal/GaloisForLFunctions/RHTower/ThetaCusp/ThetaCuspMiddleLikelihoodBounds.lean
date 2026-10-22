import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomScalePolynomials
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenCompensationSource

/-! # Complete low likelihood moments on the remaining middle interval -/
open MeasureTheory Filter Topology
namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000

private theorem secondGaussian_le {q : ℝ} (hq : 37/10 ≤ q) :
    Real.exp (-3*q) ≤ 1/50000 := by
  have h1 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num) h1 11
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he := hp.trans (Real.exp_le_exp.mpr (show (11 : ℝ) ≤ 3*q by linarith))
  have he' : (50000 : ℝ) ≤ Real.exp (3*q) := by linarith only [he]
  rw [show -3*q = -(3*q) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 50000) he'

/-- The deep calibration itself stays below one millionth throughout the middle regime. -/
theorem thetaCuspDeepTailErrorScale_le_millionth {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspDeepTailErrorScale x ≤ 1/1000000 := by
  have he : Real.exp (-8*(thetaCuspSingleAtomReflectionScale 1 x-49/20)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  unfold thetaCuspDeepTailErrorScale
  linarith only [he]

/-- The literal second atom contributes at most eight fifths of a thousandth to the first moment. -/
theorem thetaCuspSecondAtomMoment_one_le_middle {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSecondAtomMoment (thetaCuspLikelihoodCoordinate x) 1 ≤ 80/50000 := by
  let B := thetaCuspLikelihoodCoordinate x
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hBq : B = q-3/2 := thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hB : 2 ≤ B := by dsimp [q] at hBq; linarith
  have hBp : 0 < B := by linarith
  have hs : secondAtomProfile 1 B ≤ 80 := by
    change (18+54*B+48*B^(2 : ℕ))/B^(2 : ℕ) ≤ 80
    apply (div_le_iff₀ (sq_pos_of_pos hBp)).mpr
    nlinarith [mul_nonneg (show 0 ≤ B-2 by linarith) (show 0 ≤ 32*B+10 by linarith)]
  have he := secondGaussian_le hq
  have hid : thetaCuspSecondAtomMoment B 1 = Real.exp (-3*q)*secondAtomProfile 1 B := by
    rw [thetaCuspSecondAtomMoment_eq_profile 1 (by norm_num) B hBp]
    unfold secondAtomMomentProfile
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    linarith only [hBq]
  change thetaCuspSecondAtomMoment B 1 ≤ 80/50000
  rw [hid]
  calc
    _ ≤ Real.exp (-3*q)*80 := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ ≤ (1/50000)*80 := mul_le_mul_of_nonneg_right he (by norm_num)
    _ = _ := by ring

/-- The complete infinite likelihood first moment is bounded uniformly on q≥37/10. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_one_le_middle {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 1 ≤ 1/500 := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hd := thetaCuspDeepTailMoment_le_errorScale 1 (x := x) (by norm_num; linarith)
  have he := thetaCuspDeepTailErrorScale_le_millionth hq
  have hs := thetaCuspSecondAtomMoment_one_le_middle hq
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep (thetaCuspLikelihoodCoordinate_pos hx.le) 1]
  norm_num only [pow_one] at hd
  linarith only [hd, he, hs]

/-- The fixed spectral support controls mass by its first moment. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_zero_le_one {B : ℝ} (hB : 0 < B) :
    thetaCuspHigherLikelihoodSpectralMoment B 0 ≤ thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  apply integral_mono_ae (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 0 hB)
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB)
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  simp only [pow_zero, one_mul, pow_one]
  nlinarith [Real.exp_pos (-B*t)]

/-- Full source mass lies within one percent of its first atom across the middle regime. -/
theorem thetaCuspFullSource_mass_bounds_middle {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x ∧
      thetaCuspFullSource x ≤ (101/100)*thetaCuspSourceTerm x 1 := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hm := (thetaCuspHigherLikelihoodSpectralMoment_zero_le_one hB).trans
    (thetaCuspHigherLikelihoodSpectralMoment_one_le_middle hq)
  have hm0 := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := thetaCuspLikelihoodCoordinate x) 0
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
    thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
  constructor
  · nlinarith only [mul_nonneg hf.le hm0]
  · nlinarith only [mul_le_mul_of_nonneg_left hm hf.le, hf.le]

/-- Exact full-source slope decomposition through the complete first likelihood moment. -/
theorem deriv_thetaCuspFullSource_eq_likelihood_moment {x : ℝ} (hx : 0 < x) :
    deriv thetaCuspFullSource x =
      deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*
        (1+thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0)-
      2*thetaCuspSingleAtomReflectionScale 1 x*thetaCuspSourceTerm x 1*
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 1 := by
  have hd := thetaCuspFullSource_derivative_sub_first_eq 1 hx
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.sub_zero, Nat.sub_self, Nat.cast_one,
    one_mul, iteratedDeriv_zero, iteratedDeriv_one] at hd
  have hR := thetaCuspLikelihoodSourceRemainder_eq_coolingMoment hx
  have hdR := iteratedDeriv_thetaCuspLikelihoodSourceRemainder 1 hx
  simp only [iteratedDeriv_one, thetaCuspCoolingJet, thetaCuspCoolingMoment,
    Nat.cast_zero, mul_zero, zero_mul, zero_sub, zero_add, pow_one] at hdR
  simp only [thetaCuspCoolingMoment, pow_zero, one_mul] at hR
  rw [hR, hdR] at hd
  nlinarith only [hd]

end
end RHTower
