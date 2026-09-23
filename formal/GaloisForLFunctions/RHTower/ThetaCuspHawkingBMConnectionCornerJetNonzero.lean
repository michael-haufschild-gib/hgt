import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMConnectionSimpleZero
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalSlope
import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap

/-! Unconditional nonvanishing of the physical connection-corner first-jet factor. -/
open Complex Real Set
namespace RHTower.D4BMLaplaceRadial
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open D4BMJointSource
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private lemma digamma_one_im : (Complex.digamma 1).im = 0 := by
  have h := congrArg Complex.im (ReflectedDigammaAnomaly.digamma_conj (1 : ℂ))
  norm_num at h
  linarith

private def plusShiftedFactor (x t : ℝ) : ℂ :=
  (1 / 2 : ℂ) / (((x - 2 : ℝ) : ℂ) + (t : ℂ) * I) -
    2 * Complex.digamma ((x : ℂ) + (t : ℂ) * I) +
    2 / (((x - 1 : ℝ) : ℂ) + (t : ℂ) * I) +
    Complex.digamma (((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
    Complex.digamma 1

private theorem plusShiftedFactor_im_neg {x t : ℝ}
    (hx0 : 1 / 2 < x) (hx1 : x < 1) (ht : 13 / 4 < t) :
    (plusShiftedFactor x t).im < 0 := by
  have ht0 : 0 < t := by linarith
  have hxnonneg : 0 ≤ x := by linarith
  have hbnonneg : 0 ≤ x - 1 / 2 := by linarith
  have hX := im_digamma_vertical_sandwich hxnonneg ht0
  have hB := im_digamma_vertical_sandwich hbnonneg ht0
  have hxb : 0 ≤ (x - 1 / 2) / t := div_nonneg hbnonneg ht0.le
  have hxx : 0 ≤ x / t := div_nonneg hxnonneg ht0.le
  have hatanB : 0 ≤ Real.arctan ((x - 1 / 2) / t) :=
    Real.arctan_nonneg.mpr hxb
  have hatanX : Real.arctan (x / t) ≤ x / t := arctan_le_self hxx
  have hxt : x / t < 1 / t := (div_lt_div_iff_of_pos_right ht0).2 hx1
  have h3t : 3 / t < (12 / 13 : ℝ) := by
    rw [div_lt_iff₀ ht0]
    nlinarith
  have hpi : (12 / 13 : ℝ) < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hdig :
      (Complex.digamma (((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im -
          2 * (Complex.digamma ((x : ℂ) + (t : ℂ) * I)).im < 0 := by
    have hfirst :
        (Complex.digamma (((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im -
            2 * (Complex.digamma ((x : ℂ) + (t : ℂ) * I)).im ≤
          1 / t - Real.pi / 2 - Real.arctan ((x - 1 / 2) / t) +
            2 * Real.arctan (x / t) := by
      linarith [hX.1, hB.2]
    have hsecond :
        1 / t - Real.pi / 2 - Real.arctan ((x - 1 / 2) / t) +
            2 * Real.arctan (x / t) ≤
          1 / t - Real.pi / 2 + 2 * (x / t) := by
      linarith
    have hthird : 1 / t - Real.pi / 2 + 2 * (x / t) <
        3 / t - Real.pi / 2 := by
      have hthree : 3 / t = 3 * (1 / t) := by field_simp
      rw [hthree]
      linarith
    have hfourth : 3 / t - Real.pi / 2 < 0 := by linarith
    exact hfirst.trans_lt (hsecond.trans_lt (hthird.trans hfourth))
  have hden1 : 0 < (x - 2) ^ (2 : ℕ) + t ^ (2 : ℕ) := by nlinarith [sq_nonneg (x - 2), sq_pos_of_pos ht0]
  have hden2 : 0 < (x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by nlinarith [sq_nonneg (x - 1), sq_pos_of_pos ht0]
  have hr1' : (1 / 2 : ℝ) * (-t / ((x - 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num)
      (div_neg_of_neg_of_pos (neg_neg_of_pos ht0) hden1)
  have hr2' : (2 : ℝ) * (-t / ((x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ))) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num)
      (div_neg_of_neg_of_pos (neg_neg_of_pos ht0) hden2)
  unfold plusShiftedFactor
  rw [show (1 / 2 : ℂ) / (((x - 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      (1 / 2 : ℂ) * ((((x - 2 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) by rfl,
    show 2 / (((x - 1 : ℝ) : ℂ) + (t : ℂ) * I) =
      (2 : ℂ) * ((((x - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) by rfl]
  simp only [sub_im, mul_im, add_im, digamma_one_im]
  norm_num
  have hnorm1 : Complex.normSq ((x : ℂ) - 2 + (t : ℂ) * I) =
      (x - 2) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hnorm2 : Complex.normSq ((x : ℂ) - 1 + (t : ℂ) * I) =
      (x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [hnorm1, hnorm2]
  have hpoint : (x : ℂ) - 1 / 2 + (t : ℂ) * I =
      (((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    push_cast
    ring
  rw [hpoint]
  nlinarith [hr1', hr2', hdig]

private def minusShiftedFactor (x t : ℝ) : ℂ :=
  (1 / 2 : ℂ) / (((x - 2 : ℝ) : ℂ) + (t : ℂ) * I) -
    2 * Complex.digamma ((x : ℂ) + (t : ℂ) * I) +
    2 / (((x - 1 : ℝ) : ℂ) + (t : ℂ) * I) +
    Complex.digamma (((x + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) -
    1 / (((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
    Complex.digamma 1

private theorem minusShiftedFactor_im_neg {x t : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / 2) (ht : 13 / 4 < t) :
    (minusShiftedFactor x t).im < 0 := by
  have ht0 : 0 < t := by linarith
  have hxnonneg : 0 ≤ x := hx0.le
  have hynonneg : 0 ≤ x + 1 / 2 := by linarith
  have hX := im_digamma_vertical_sandwich hxnonneg ht0
  have hY := im_digamma_vertical_sandwich hynonneg ht0
  have hydiv : 0 ≤ (x + 1 / 2) / t := div_nonneg hynonneg ht0.le
  have hxdiv : 0 ≤ x / t := div_nonneg hxnonneg ht0.le
  have hatanY : 0 ≤ Real.arctan ((x + 1 / 2) / t) :=
    Real.arctan_nonneg.mpr hydiv
  have hatanX : Real.arctan (x / t) ≤ x / t := arctan_le_self hxdiv
  have hxt : 2 * (x / t) < 1 / t := by
    have hxdiv' : x / t < (1 / 2) / t := (div_lt_div_iff_of_pos_right ht0).2 hx1
    have hhalf : (2 : ℝ) * ((1 / 2) / t) = 1 / t := by field_simp
    rw [← hhalf]
    nlinarith
  have h2t : 2 / t < (8 / 13 : ℝ) := by
    rw [div_lt_iff₀ ht0]
    nlinarith
  have hpi : (8 / 13 : ℝ) < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hdig :
      (Complex.digamma (((x + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im -
          2 * (Complex.digamma ((x : ℂ) + (t : ℂ) * I)).im < 0 := by
    have hfirst :
        (Complex.digamma (((x + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im -
            2 * (Complex.digamma ((x : ℂ) + (t : ℂ) * I)).im ≤
          1 / t - Real.pi / 2 - Real.arctan ((x + 1 / 2) / t) +
            2 * Real.arctan (x / t) := by
      linarith [hX.1, hY.2]
    have hsecond :
        1 / t - Real.pi / 2 - Real.arctan ((x + 1 / 2) / t) +
            2 * Real.arctan (x / t) ≤
          1 / t - Real.pi / 2 + 2 * (x / t) := by
      linarith
    have hthird : 1 / t - Real.pi / 2 + 2 * (x / t) <
        2 / t - Real.pi / 2 := by
      have htwo : 2 / t = 2 * (1 / t) := by field_simp
      rw [htwo]
      linarith
    have hfourth : 2 / t - Real.pi / 2 < 0 := by linarith
    exact hfirst.trans_lt (hsecond.trans_lt (hthird.trans hfourth))
  have hdenW : 0 < (x - 2) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x - 2), sq_pos_of_pos ht0]
  have hdenZ : 0 < (x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x - 1), sq_pos_of_pos ht0]
  have hdenO : 0 < (x - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_pos_of_pos ht0]
  have hinvcompare : 1 / ((x - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ)) <
      2 / ((x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
    rw [div_lt_div_iff₀ hdenO hdenZ]
    nlinarith
  have hrW : (1 / 2 : ℝ) * (-t / ((x - 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num)
      (div_neg_of_neg_of_pos (neg_neg_of_pos ht0) hdenW)
  have hrPair : (2 : ℝ) * (-t / ((x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ))) -
      (-t / ((x - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) < 0 := by
    have htinv := mul_lt_mul_of_pos_left hinvcompare ht0
    have heq : (2 : ℝ) * (-t / ((x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ))) -
        (-t / ((x - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) =
      t * (1 / ((x - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ))) -
        t * (2 / ((x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ))) := by ring
    rw [heq]
    linarith
  unfold minusShiftedFactor
  rw [show (1 / 2 : ℂ) / (((x - 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      (1 / 2 : ℂ) * ((((x - 2 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) by rfl,
    show 2 / (((x - 1 : ℝ) : ℂ) + (t : ℂ) * I) =
      (2 : ℂ) * ((((x - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) by rfl,
    show 1 / (((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      ((((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) by rw [one_div]]
  simp only [sub_im, mul_im, add_im, digamma_one_im]
  norm_num
  have hnormW : Complex.normSq ((x : ℂ) - 2 + (t : ℂ) * I) =
      (x - 2) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hnormZ : Complex.normSq ((x : ℂ) - 1 + (t : ℂ) * I) =
      (x - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hnormO : Complex.normSq ((x : ℂ) - 1 / 2 + (t : ℂ) * I) =
      (x - 1 / 2) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [hnormW, hnormZ, hnormO]
  have hpoint : (x : ℂ) + 1 / 2 + (t : ℂ) * I =
      (((x + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    push_cast
    ring
  rw [hpoint]
  nlinarith [hrW, hrPair, hdig]

private theorem plusShiftedFactor_neg_eq_conj (x t : ℝ) :
    plusShiftedFactor x (-t) = starRingEnd ℂ (plusShiftedFactor x t) := by
  have hdig (a : ℝ) :
      Complex.digamma ((a : ℂ) + ((-t : ℝ) : ℂ) * I) =
        starRingEnd ℂ (Complex.digamma ((a : ℂ) + (t : ℂ) * I)) := by
    rw [← ReflectedDigammaAnomaly.digamma_conj]
    congr 1
    apply Complex.ext <;> simp
  have hdiv (c : ℂ) (hc : starRingEnd ℂ c = c) (a : ℝ) :
      c / ((a : ℂ) + ((-t : ℝ) : ℂ) * I) =
        starRingEnd ℂ (c / ((a : ℂ) + (t : ℂ) * I)) := by
    rw [map_div₀]
    congr 1
    · exact hc.symm
    · apply Complex.ext <;> simp
  unfold plusShiftedFactor
  rw [hdiv (1 / 2) (by simp only [map_div₀, map_one, map_ofNat]) (x - 2),
    hdiv 2 (by simp only [map_ofNat]) (x - 1),
    hdig x, hdig (x - 1 / 2)]
  rw [Complex.digamma_one]
  simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_one, map_ofNat,
    Complex.conj_ofReal]

private theorem minusShiftedFactor_neg_eq_conj (x t : ℝ) :
    minusShiftedFactor x (-t) = starRingEnd ℂ (minusShiftedFactor x t) := by
  have hdig (a : ℝ) :
      Complex.digamma ((a : ℂ) + ((-t : ℝ) : ℂ) * I) =
        starRingEnd ℂ (Complex.digamma ((a : ℂ) + (t : ℂ) * I)) := by
    rw [← ReflectedDigammaAnomaly.digamma_conj]
    congr 1
    apply Complex.ext <;> simp
  have hdiv (c : ℂ) (hc : starRingEnd ℂ c = c) (a : ℝ) :
      c / ((a : ℂ) + ((-t : ℝ) : ℂ) * I) =
        starRingEnd ℂ (c / ((a : ℂ) + (t : ℂ) * I)) := by
    rw [map_div₀]
    congr 1
    · exact hc.symm
    · apply Complex.ext <;> simp
  unfold minusShiftedFactor
  rw [hdiv (1 / 2) (by simp only [map_div₀, map_one, map_ofNat]) (x - 2),
    hdiv 2 (by simp only [map_ofNat]) (x - 1),
    hdiv 1 (by simp only [map_one]) (x - 1 / 2), hdig x, hdig (x + 1 / 2)]
  rw [Complex.digamma_one]
  simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_one, map_ofNat,
    Complex.conj_ofReal]

private theorem plusShiftedFactor_ne_zero {x t : ℝ}
    (hx0 : 1 / 2 < x) (hx1 : x < 1) (ht : 13 / 4 < |t|) :
    plusShiftedFactor x t ≠ 0 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · have hheight : 13 / 4 < -t := by simpa [abs_of_neg htneg] using ht
    have hne : plusShiftedFactor x (-t) ≠ 0 := by
      intro hzero
      have him := plusShiftedFactor_im_neg hx0 hx1 hheight
      rw [hzero] at him
      norm_num at him
    intro hzero
    have hsym := plusShiftedFactor_neg_eq_conj x (-t)
    simp only [neg_neg] at hsym
    rw [hzero] at hsym
    apply hne
    have hc := congrArg (starRingEnd ℂ) hsym
    simpa using hc.symm
  · have hheight : 13 / 4 < t := by simpa [abs_of_pos htpos] using ht
    intro hzero
    have him := plusShiftedFactor_im_neg hx0 hx1 hheight
    rw [hzero] at him
    norm_num at him

private theorem minusShiftedFactor_ne_zero {x t : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / 2) (ht : 13 / 4 < |t|) :
    minusShiftedFactor x t ≠ 0 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · have hheight : 13 / 4 < -t := by simpa [abs_of_neg htneg] using ht
    have hne : minusShiftedFactor x (-t) ≠ 0 := by
      intro hzero
      have him := minusShiftedFactor_im_neg hx0 hx1 hheight
      rw [hzero] at him
      norm_num at him
    intro hzero
    have hsym := minusShiftedFactor_neg_eq_conj x (-t)
    simp only [neg_neg] at hsym
    rw [hzero] at hsym
    apply hne
    have hc := congrArg (starRingEnd ℂ) hsym
    simpa using hc.symm
  · have hheight : 13 / 4 < t := by simpa [abs_of_pos htpos] using ht
    intro hzero
    have him := minusShiftedFactor_im_neg hx0 hx1 hheight
    rw [hzero] at him
    norm_num at him

def physicalConnectionCornerJetFactor (q : XiZeroCopy) (side : Bool) : ℂ :=
  1 / (2 * physicalFundamentalFrequency q side) -
    2 * Complex.digamma (gaussC (physicalFundamentalFrequency q side)) +
    Complex.digamma (connectionOtherArgument
      (physicalFundamentalFrequency q side) (physicalRadialFrequency q) side) +
    Complex.digamma 1

private theorem xiZeroCopy_thirteen_halves_lt_abs_im (q : XiZeroCopy) :
    13 / 2 < |(q.1 : ℂ).im| := by
  have hsq :=
    xiZeroCopy_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq q
  nlinarith [sq_abs (q.1 : ℂ).im, abs_nonneg (q.1 : ℂ).im]

private theorem physicalConnectionCornerJetFactor_true_eq (q : XiZeroCopy) :
    physicalConnectionCornerJetFactor q true =
      plusShiftedFactor (1 - (q.1 : ℂ).re / 2) (-(q.1 : ℂ).im / 2) := by
  let rho : ℂ := q.1
  change physicalConnectionCornerJetFactor q true =
    plusShiftedFactor (1 - rho.re / 2) (-rho.im / 2)
  have hrhoim : rho.im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hoff : ∀ m : ℕ, -rho / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hrhoim
    have him := congrArg Complex.im h
    norm_num [Complex.div_im] at him
    linarith
  have hrec := Complex.digamma_apply_add_one (-rho / 2) hoff
  have hrec' : Complex.digamma (1 - rho / 2) =
      Complex.digamma (-rho / 2) + (-rho / 2)⁻¹ := by
    convert hrec using 1 <;> ring
  have hfreq : physicalFundamentalFrequency q true = -1 - rho / 2 := by
    simpa only [rho, if_pos] using physicalFundamentalFrequency_eq q true
  have hC : gaussC (physicalFundamentalFrequency q true) = -rho / 2 := by
    rw [hfreq]
    unfold gaussC
    ring
  have hO : connectionOtherArgument (physicalFundamentalFrequency q true)
      (physicalRadialFrequency q) true = (1 - rho) / 2 := by
    rw [hfreq]
    simp only [connectionOtherArgument, if_pos]
    unfold gaussC gaussA physicalRadialFrequency
    rw [physicalAngularParameter_eq]
    ring_nf
    rw [I_sq]
    ring
  have hW : ((((1 - rho.re / 2) - 2 : ℝ) : ℂ) +
      ((-rho.im / 2 : ℝ) : ℂ) * I) = -1 - rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hZ : ((((1 - rho.re / 2) - 1 : ℝ) : ℂ) +
      ((-rho.im / 2 : ℝ) : ℂ) * I) = -rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hX : (((1 - rho.re / 2 : ℝ) : ℂ) +
      ((-rho.im / 2 : ℝ) : ℂ) * I) = 1 - rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hB : ((((1 - rho.re / 2) - 1 / 2 : ℝ) : ℂ) +
      ((-rho.im / 2 : ℝ) : ℂ) * I) = (1 - rho) / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  unfold physicalConnectionCornerJetFactor plusShiftedFactor
  rw [hC, hO, hfreq, hW, hZ, hX, hB, hrec']
  rw [show 1 / (2 * (-1 - rho / 2)) =
      (1 / 2 : ℂ) / (-1 - rho / 2) by field_simp]
  ring

private theorem physicalConnectionCornerJetFactor_false_eq (q : XiZeroCopy) :
    physicalConnectionCornerJetFactor q false =
      minusShiftedFactor ((q.1 : ℂ).re / 2) ((q.1 : ℂ).im / 2) := by
  let rho : ℂ := q.1
  change physicalConnectionCornerJetFactor q false =
    minusShiftedFactor (rho.re / 2) (rho.im / 2)
  have hrhoim : rho.im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hoffZ : ∀ m : ℕ, -1 + rho / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hrhoim
    have him := congrArg Complex.im h
    norm_num [Complex.div_im] at him
    linarith
  have hoffO : ∀ m : ℕ, -1 / 2 + rho / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hrhoim
    have him := congrArg Complex.im h
    norm_num [Complex.div_im] at him
    linarith
  have hrecZ := Complex.digamma_apply_add_one (-1 + rho / 2) hoffZ
  have hrecO := Complex.digamma_apply_add_one (-1 / 2 + rho / 2) hoffO
  have hrecZ' : Complex.digamma (rho / 2) =
      Complex.digamma (-1 + rho / 2) + (-1 + rho / 2)⁻¹ := by
    convert hrecZ using 1 <;> ring
  have hrecO' : Complex.digamma (1 / 2 + rho / 2) =
      Complex.digamma (-1 / 2 + rho / 2) + (-1 / 2 + rho / 2)⁻¹ := by
    convert hrecO using 1 <;> ring
  have hfreq : physicalFundamentalFrequency q false = -2 + rho / 2 := by
    simpa only [rho, Bool.false_eq_true, if_false] using
      physicalFundamentalFrequency_eq q false
  have hC : gaussC (physicalFundamentalFrequency q false) = -1 + rho / 2 := by
    rw [hfreq]
    unfold gaussC
    ring
  have hO : connectionOtherArgument (physicalFundamentalFrequency q false)
      (physicalRadialFrequency q) false = -1 / 2 + rho / 2 := by
    rw [hfreq]
    simp only [connectionOtherArgument, Bool.false_eq_true, if_false]
    unfold gaussC gaussB physicalRadialFrequency
    rw [physicalAngularParameter_eq]
    ring_nf
    rw [I_sq]
    ring
  have hW : (((rho.re / 2 - 2 : ℝ) : ℂ) +
      ((rho.im / 2 : ℝ) : ℂ) * I) = -2 + rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hZ : (((rho.re / 2 - 1 : ℝ) : ℂ) +
      ((rho.im / 2 : ℝ) : ℂ) * I) = -1 + rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hX : (((rho.re / 2 : ℝ) : ℂ) +
      ((rho.im / 2 : ℝ) : ℂ) * I) = rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hY : (((rho.re / 2 + 1 / 2 : ℝ) : ℂ) +
      ((rho.im / 2 : ℝ) : ℂ) * I) = 1 / 2 + rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hOpoint : (((rho.re / 2 - 1 / 2 : ℝ) : ℂ) +
      ((rho.im / 2 : ℝ) : ℂ) * I) = -1 / 2 + rho / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  unfold physicalConnectionCornerJetFactor minusShiftedFactor
  rw [hC, hO, hfreq, hW, hZ, hX, hY, hOpoint, hrecZ', hrecO']
  rw [show 1 / (2 * (-2 + rho / 2)) =
      (1 / 2 : ℂ) / (-2 + rho / 2) by field_simp]
  ring

theorem physicalConnectionCornerJetFactor_ne_zero (q : XiZeroCopy) (side : Bool) :
    physicalConnectionCornerJetFactor q side ≠ 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hheight := xiZeroCopy_thirteen_halves_lt_abs_im q
  cases side
  · rw [physicalConnectionCornerJetFactor_false_eq]
    apply minusShiftedFactor_ne_zero
    · nlinarith [hstrip.1]
    · nlinarith [hstrip.2]
    · rw [abs_div]
      norm_num
      nlinarith
  · rw [physicalConnectionCornerJetFactor_true_eq]
    apply plusShiftedFactor_ne_zero
    · nlinarith [hstrip.2]
    · nlinarith [hstrip.1]
    · rw [abs_div, abs_neg]
      norm_num
      nlinarith

end
end RHTower.D4BMLaplaceRadial
