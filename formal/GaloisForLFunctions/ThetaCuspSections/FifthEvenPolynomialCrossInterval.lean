import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegimeOneKey

/-!
# A positive interval across the quartic profile zero

On the interval `1/2 ≤ x²`, `0 ≤ x ≤ 3/4`, the complete source satisfies
`F' ≥ -24 F`. Factoring the profiled correction at its double zero then
gives a nonnegative correction, so native fifth-even positivity applies.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit

namespace GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
open FifthCrossEnvelope FifthNativeRay EvenFiveEndpoint

private theorem interval_scale_bounds {x : ℝ} (hx : 0 ≤ x)
    (hl : (1/2 : ℝ) ≤ x^2) (hu : x ≤ 3/4) :
    7 ≤ thetaCuspSingleAtomReflectionScale 1 x ∧
      thetaCuspSingleAtomReflectionScale 1 x ≤ 57/4 := by
  have hxhalf : (1/2 : ℝ) ≤ x := by
    by_contra h
    have hm := mul_nonneg (show 0 ≤ (1/2 : ℝ)-x by linarith only [h])
      (show 0 ≤ (1/2 : ℝ)+x by linarith only [hx])
    nlinarith only [hm,hl]
  have helo : (5/2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 3
    norm_num [Finset.sum_range_succ,Nat.factorial] at h
    linarith only [h]
  have hexlo := Real.exp_le_exp.mpr (show (1 : ℝ) ≤ 2*x by linarith only [hxhalf])
  have hprodlo := mul_le_mul (le_of_lt Real.pi_gt_three) (helo.trans hexlo)
    (by norm_num : (0 : ℝ) ≤ 5/2) Real.pi_pos.le
  have hehi : Real.exp (3/2 : ℝ) ≤ 9/2 := by
    linarith only [exp_threeHalves_bounds.2]
  have hexhi := Real.exp_le_exp.mpr (show 2*x ≤ (3/2 : ℝ) by linarith only [hu])
  have hprodhi := mul_le_mul (le_of_lt Real.pi_lt_d2) (hexhi.trans hehi)
    (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 3.15)
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
  constructor <;> linarith only [hprodlo,hprodhi]

private theorem interval_slope_bound {x : ℝ} (hx : 0 ≤ x)
    (hl : (1/2 : ℝ) ≤ x^2) (hu : x ≤ 3/4) :
    -24*thetaCuspFullSource x ≤ deriv thetaCuspFullSource x := by
  obtain ⟨hqlo,hqhi⟩ := interval_scale_bounds hx hl hu
  let q := thetaCuspSingleAtomReflectionScale 1 x
  change q ≤ 57/4 at hqhi
  have hden : 0 < 2*(2*q-3) := by dsimp only [q]; linarith only [hqlo]
  have hs : firstSlope q ≤ (239/10 : ℝ) := by
    have hm := mul_nonneg
      (show 0 ≤ (57/4 : ℝ)-q by dsimp only [q]; linarith only [hqhi])
      (show 0 ≤ 2*q-3 by linarith only [hden])
    unfold firstSlope
    apply (div_le_iff₀ hden).2
    nlinarith only [hm,hqhi]
  have hmass := mass_slope_bounds hqlo
  have hxp : 0 < x := by
    rcases eq_or_lt_of_le hx with he | hp
    · rw [← he] at hl
      norm_num at hl
    · exact hp
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hxp (by norm_num : 0 < (1 : ℕ))
  have hm := mul_le_mul_of_nonneg_right hs hf.le
  change (firstSlope q)*thetaCuspSourceTerm x 1 ≤ _ at hm
  change thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x ∧
    thetaCuspFullSource x ≤ (1000001/1000000)*thetaCuspSourceTerm x 1 ∧
    -(firstSlope q+1/100000)*thetaCuspSourceTerm x 1 ≤ deriv thetaCuspFullSource x at hmass
  nlinarith only [hm,hmass.1,hmass.2.2,hf.le]

/-- Across the profile zero, its exact correction has an explicit nonnegative reserve. -/
theorem compensation_interval_lower {x : ℝ} (hx : 0 ≤ x)
    (hl : (1/2 : ℝ) ≤ x^2) (hu : x ≤ 3/4) :
    (3/8 : ℝ)*(2*x^2-1)*thetaCuspFullSource x^2 ≤ compensation x := by
  let t := 2*x^2-1
  have ht : 0 ≤ t := by dsimp only [t]; linarith only [hl]
  have hxsq := mul_self_le_mul_self hx hu
  have hthi : t ≤ (1/8 : ℝ) := by dsimp only [t]; nlinarith only [hxsq]
  have hxt := mul_nonneg (show 0 ≤ (3/4 : ℝ)-x by linarith only [hu]) ht
  have hc : 0 ≤ 4+(7-48*x)*t-3/8 := by nlinarith only [hxt,hthi]
  have hF := (thetaCuspFullSource_pos_all x).le
  have hd : 0 ≤ deriv thetaCuspFullSource x+24*thetaCuspFullSource x := by
    linarith only [interval_slope_bound hx hl hu]
  have hp := add_nonneg
    (mul_nonneg (show 0 ≤ 2*x*t^2*thetaCuspFullSource x by positivity) hd)
    (mul_nonneg (mul_nonneg ht (sq_nonneg (thetaCuspFullSource x))) hc)
  have he : compensation x-(3/8)*t*thetaCuspFullSource x^2 =
      (2*x*t^2*thetaCuspFullSource x)*
        (deriv thetaCuspFullSource x+24*thetaCuspFullSource x)+
      (t*thetaCuspFullSource x^2)*(4+(7-48*x)*t-3/8) := by
    dsimp only [compensation,thetaCuspCenterCompensationSource,t]
    ring
  rw [← he] at hp
  exact sub_nonneg.mp hp

/-- The complete profiled fifth even source is positive throughout an explicit interval. -/
theorem repair_interval_posDef {x : ℝ} (hx : 0 ≤ x)
    (hl : (1/2 : ℝ) ≤ x^2) (hu : x ≤ 3/4) : (repair x).PosDef := by
  have hq := (interval_scale_bounds hx hl hu).1
  have hnative := native_even_five_posDef (show 5 ≤ thetaCuspSingleAtomReflectionScale 1 x by
    linarith only [hq])
  have ht : 0 ≤ 2*x^2-1 := by linarith only [hl]
  have hcomp : 0 ≤ compensation x :=
    (by positivity : 0 ≤ (3/8 : ℝ)*(2*x^2-1)*thetaCuspFullSource x^2).trans
      (compensation_interval_lower hx hl hu)
  exact hnative.add_posSemidef
    ((crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap).smul hcomp)

/-- The same interval is positive for the literal weighted source at every positive aperture. -/
theorem weightedRepair_interval_posDef {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hl : (2 : ℝ) ≤ r^2) (hu : r ≤ 3/2) : (weightedRepair a r).PosDef := by
  have hx : 0 ≤ r/2 := by positivity
  have hxl : (1/2 : ℝ) ≤ (r/2)^2 := by nlinarith only [hl]
  have hxu : r/2 ≤ (3/4 : ℝ) := by linarith only [hu]
  have hw := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hrem := sub_nonneg.mpr (deriv_flux_lower ha.le hr.le)
  rw [weightedRepair_decomposition]
  exact ((repair_interval_posDef hx hxl hxu).smul hw).add_posSemidef
    ((crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap).smul hrem)

end GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
