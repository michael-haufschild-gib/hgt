import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceInnerTransport
import GaloisForLFunctions.RHTower.ThetaCuspDeepTailCoolingTwelve
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomAffineEvenFour

/-!
# Stronger full-source estimates on the inner scale interval

The complete deep tail admits coefficient three quarters at derivatives six
through twelve because exponential transport retains the alternating score.
The complete center correction also carries an additional positive reserve
on the lower subinterval. Both estimates retain every atom of the source.
-/
open MeasureTheory Filter Topology
namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000
/-- High derivatives admit coefficient three quarters after preserving signed score cancellation. -/
theorem abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_inner_transport
    {n : ℕ} (hn : 6 ≤ n) (hnu : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      (3/4 : ℝ)*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hqp : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  rw [iteratedDeriv_thetaCuspDeepLikelihoodRemainder n hx]
  have hsigned := (thetaCuspDeepCoolingJet_signed_le_leadingMoment_twelve hnu hq).1
  have habs : |thetaCuspDeepCoolingJet n 0 x| =
      (-1 : ℝ)^n*thetaCuspDeepCoolingJet n 0 x := by
    rw [← abs_of_nonneg hsigned,abs_mul,abs_pow]
    norm_num
  rw [habs]
  let C := (3/4 : ℝ)*(16*thetaCuspSingleAtomReflectionScale 1 x)^n*
    Real.exp (-8*(thetaCuspSingleAtomReflectionScale 1 x-49/20))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : (-1 : ℝ)^n*thetaCuspDeepCoolingJet n 0 x ≤
      C*thetaCuspDeepTailMoment (19/20) 0 := by
    rw [thetaCuspDeepCoolingJet_eq_integral_score n 0 hB,← integral_const_mul,
      thetaCuspDeepTailMoment,← integral_const_mul]
    apply integral_mono_ae ((integrable_laplaceCoolingJet_mul_exp_deep n 0 hB).const_mul _)
      ((integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure 0 (by norm_num : (0 : ℝ) < 19/20)).const_mul _)
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    have hp := HTGeometry.laplaceCoolingJet_inner_transport hn hnu hq hqu ht
    have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    have he : Real.exp ((thetaCuspSingleAtomReflectionScale 1 x-49/20)*(t-8))*
        Real.exp (-thetaCuspLikelihoodCoordinate x*t) =
        Real.exp (-8*(thetaCuspSingleAtomReflectionScale 1 x-49/20))*
          Real.exp (-(19/20)*t) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      rw [thetaCuspSingleAtomScale_likelihoodCoordinate]
      ring
    simp only [pow_zero,one_mul]
    calc
      _ = ((-1 : ℝ)^n*HTGeometry.laplaceCoolingJet n 0
          (thetaCuspSingleAtomReflectionScale 1 x*t))*Real.exp (-thetaCuspLikelihoodCoordinate x*t) := by ring
      _ ≤ _ := hm
      _ = _ := by dsimp [C]; rw [mul_assoc,he]; ring
  have hm := mul_le_mul_of_nonneg_left thetaCuspDeepTailMoment_calibration hC
  apply hb.trans
  calc
    _ ≤ C*(1/1000000) := hm
    _ = _ := by dsimp [C,thetaCuspDeepTailErrorScale]; ring


/-- The affine full-source slope gives an additional correction reserve at the lower inner scales. -/
theorem thetaCuspCenterCompensationSource_quadratic_lower_inner {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 9/2) :
    (1+(9/5)*thetaCuspSingleAtomReflectionScale 1 x-
      (2/5)*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ))*thetaCuspFullSource x^(2 : ℕ) ≤
      thetaCuspCenterCompensationSource x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hF := thetaCuspFullSource_pos_all x
  have hd := mul_le_mul_of_nonneg_left
    (thetaCuspFullSource_slope_affine_lower_middle hq (by linarith : thetaCuspSingleAtomReflectionScale 1 x ≤ 7))
    (show 0 ≤ 2*x*thetaCuspFullSource x by positivity)
  have hc := ten_mul_center_add_five_halves_le_firstAtomScale hx.le
  have hr := mul_nonneg
    (show 0 ≤ thetaCuspSingleAtomReflectionScale 1 x-10*x-5/2 by linarith)
    (show 0 ≤ (2*thetaCuspSingleAtomReflectionScale 1 x-4)*thetaCuspFullSource x^(2 : ℕ) by
      apply mul_nonneg (by linarith) (sq_nonneg _))
  unfold thetaCuspCenterCompensationSource
  nlinarith only [hd,hr]

/-- The additional lower-scale correction is positive in the first-atom normalization. -/
theorem thetaCuspCenterCompensationSource_firstAtom_extra_inner {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 9/2) :
    ((11/2-thetaCuspSingleAtomReflectionScale 1 x)+
      (2/5)*(thetaCuspSingleAtomReflectionScale 1 x-5/2)*
        (9/2-thetaCuspSingleAtomReflectionScale 1 x))*thetaCuspSourceTerm x 1^(2 : ℕ) ≤
      thetaCuspCenterCompensationSource x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hm := pow_le_pow_left₀ hf.le (thetaCuspFullSource_mass_bounds_middle hq).1 2
  have hC : 0 ≤ (11/2-thetaCuspSingleAtomReflectionScale 1 x)+
      (2/5)*(thetaCuspSingleAtomReflectionScale 1 x-5/2)*(9/2-thetaCuspSingleAtomReflectionScale 1 x) := by
    have h1 : 0 ≤ 11/2-thetaCuspSingleAtomReflectionScale 1 x := by linarith
    have h2 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x-5/2 := by linarith
    have h3 : 0 ≤ 9/2-thetaCuspSingleAtomReflectionScale 1 x := by linarith
    positivity
  apply (mul_le_mul_of_nonneg_left hm hC).trans
  have he (q : ℝ) : (11/2-q)+(2/5)*(q-5/2)*(9/2-q) = 1+(9/5)*q-(2/5)*q^(2 : ℕ) := by ring
  rw [he]
  exact thetaCuspCenterCompensationSource_quadratic_lower_inner hq hqu


end
end RHTower
