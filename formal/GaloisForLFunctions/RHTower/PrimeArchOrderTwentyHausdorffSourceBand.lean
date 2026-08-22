import GaloisForLFunctions.RHTower.PrimeArchExtendedHausdorffSourceBand
import GaloisForLFunctions.RHTower.XiCenteredOrderNineteenSourceBudgetClosure

/-!
# Order-twenty endpoint Hausdorff source band

The fourth-trace budget makes every twentieth reciprocal-square power strictly
right-facing.  This crosses the sector-only `k = 18` boundary in the endpoint
Hausdorff lattice.  Because the endpoint-complement factor has opposite phase,
all complement powers through `r = 57` preserve that right-facing sign.

Consequently the unconditional endpoint rectangle extends from `19 × 58` to
`20 × 58`, adding the complete `k = 19` row without any zero table or height
computation.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem re_twentieth_pow_mul_pow_nonneg_of_opposite_phase
    (z w : ℂ) (r : ℕ)
    (hzre : 0 < z.re) (hwre : 0 < w.re)
    (hwim : w.im = -z.im)
    (hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re)
    (hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re)
    (hzpow : 0 < (z ^ 20).re) (hr : r ≤ 57) :
    0 ≤ (z ^ 20 * w ^ r).re := by
  have hzarg : |z.arg| ≤ (10 / 121 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by nlinarith)
  have hwarg : |w.arg| ≤ (10 / 363 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by nlinarith)
  let x : ℝ := 20 * z.arg
  let y : ℝ := (r : ℝ) * w.arg
  have hxcoarse : |x| ≤ (200 / 121 : ℝ) := by
    calc
      |x| = 20 * |z.arg| := by simp only [x, abs_mul, abs_ofNat]
      _ ≤ 20 * (10 / 121 : ℝ) := mul_le_mul_of_nonneg_left hzarg (by norm_num)
      _ = 200 / 121 := by ring
  have hxpi : |x| < Real.pi := by
    exact hxcoarse.trans_lt (by nlinarith [Real.pi_gt_d20])
  have hnorm : 0 < ‖z‖ ^ 20 := by
    apply pow_pos
    exact norm_pos_iff.mpr (fun hz => by simpa [hz] using hzre.ne')
  have hpolar : (z ^ 20).re = ‖z‖ ^ 20 * Real.cos x := by
    simpa only [x, Nat.cast_ofNat, pow_zero, norm_one, mul_one, zero_mul, add_zero,
      mul_one] using pow_mul_pow_re_eq_norm_cos z 1 20 0
  have hcosx : 0 < Real.cos x := by
    rw [hpolar] at hzpow
    exact pos_of_mul_pos_left hzpow hnorm.le
  have hx : |x| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · by_contra h
      have hnegxLower : Real.pi / 2 ≤ -x := by linarith
      have hnegxUpper : -x ≤ Real.pi + Real.pi / 2 := by
        rw [abs_lt] at hxpi
        linarith [Real.pi_pos]
      have hnonpos :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hnegxLower hnegxUpper
      rw [Real.cos_neg] at hnonpos
      linarith
    · by_contra h
      have hxLower : Real.pi / 2 ≤ x := by linarith
      have hxUpper : x ≤ Real.pi + Real.pi / 2 := by
        rw [abs_lt] at hxpi
        linarith [Real.pi_pos]
      have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le hxLower hxUpper
      linarith
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrR : (r : ℝ) ≤ 57 := by exact_mod_cast hr
  have hy : |y| < Real.pi / 2 := by
    have hyBound : |y| ≤ (190 / 121 : ℝ) := by
      calc
        |y| = (r : ℝ) * |w.arg| := by
          simp only [y, abs_mul, abs_of_nonneg hr0]
        _ ≤ (r : ℝ) * (10 / 363 : ℝ) :=
          mul_le_mul_of_nonneg_left hwarg hr0
        _ ≤ 190 / 121 := by nlinarith
    exact hyBound.trans_lt (by nlinarith [Real.pi_gt_d20])
  have hangle : x + y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_lt] at hx hy
    by_cases hzim : 0 ≤ z.im
    · have hzarg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzim
      have hwim0 : w.im ≤ 0 := by rw [hwim]; linarith
      have hwarg0 : w.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hwre]
        exact Real.arctan_nonpos.mpr (div_nonpos_of_nonpos_of_nonneg hwim0 hwre.le)
      have hx0 : 0 ≤ x := mul_nonneg (by norm_num) hzarg0
      have hy0 : y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hwarg0
      constructor
      · exact hy.1.trans_le (by linarith)
      · exact (by linarith : x + y ≤ x).trans_lt hx.2
    · have hzim0 : z.im ≤ 0 := le_of_not_ge hzim
      have hzarg0 : z.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hzre]
        exact Real.arctan_nonpos.mpr (div_nonpos_of_nonpos_of_nonneg hzim0 hzre.le)
      have hwim0 : 0 ≤ w.im := by rw [hwim]; linarith
      have hwarg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hwim0
      have hx0 : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) hzarg0
      have hy0 : 0 ≤ y := mul_nonneg hr0 hwarg0
      constructor
      · exact hx.1.trans_le (by linarith)
      · exact (by linarith : x + y ≤ y).trans_lt hy.2
  rw [pow_mul_pow_re_eq_norm_cos]
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg z) 20) (pow_nonneg (norm_nonneg w) r))
    (Real.cos_pos_of_mem_Ioo (by simpa only [x, y, Nat.cast_ofNat] using hangle)).le

/-- The complete `k = 19`, `r ≤ 57` endpoint Hausdorff row is atomwise nonnegative. -/
theorem re_xiCentral_scaledBasis_orderTwentyRow_nonneg
    (q : XiZeroCopy) (r : ℕ) (hr : r ≤ 57) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 20 *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  let w : ℂ := (R : ℂ) - z
  have hzre : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hzReal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hwReal : w = ((R - z.re : ℝ) : ℂ) := by
      dsimp only [w]
      rw [hzReal]
      norm_num
    have hzleR : z.re ≤ R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q
    change 0 ≤ (z ^ 20 * w ^ r).re
    rw [hzReal, hwReal]
    norm_cast
    exact mul_nonneg (pow_nonneg hzre.le 20)
      (pow_nonneg (sub_nonneg.mpr hzleR) r)
  · have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hon
    have hwre : 0 < w.re := by
      dsimp only [w]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re := by
      simpa only [z] using
        twelvePointOne_mul_abs_im_xiZeroCopyReciprocalSquare_le_re q
    have hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re := by
      dsimp only [w]
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
        Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hwim : w.im = -z.im := by
      dsimp only [w]
      simp
    have hzpow : 0 < (z ^ 20).re := by
      simpa only [z] using xiZeroCopyReciprocalSquare_pow_twenty_re_pos q
    change 0 ≤ (z ^ 20 * w ^ r).re
    exact re_twentieth_pow_mul_pow_nonneg_of_opposite_phase
      z w r hzre hwre hwim hzsector hwsector hzpow hr

/-- The endpoint Hausdorff rectangle extends unconditionally to `k ≤ 19`, `r ≤ 57`. -/
theorem re_xiCentral_scaledBasis_orderTwentyRectangle_nonneg
    (q : XiZeroCopy) (k r : ℕ) (hk : k ≤ 19) (hr : r ≤ 57) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ (k + 1) *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  rcases lt_or_eq_of_le hk with hk' | rfl
  · exact re_xiCentral_scaledBasis_extendedRectangle_nonneg q k r (by omega) hr
  · norm_num
    exact re_xiCentral_scaledBasis_orderTwentyRow_nonneg q r hr

/-- The `20 × 58` endpoint Hausdorff rectangle is unconditionally nonnegative. -/
theorem scaledPrimeArchEndpointHausdorffDifference_orderTwentyRectangle_nonnegative
    (k r : ℕ) (hk : k ≤ 19) (hr : r ≤ 57) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius k r)]
  apply tsum_nonneg
  intro q
  exact re_xiCentral_scaledBasis_orderTwentyRectangle_nonneg q k r hk hr

/-- The enlarged rectangle contains exactly 1160 indexed inequalities. -/
theorem primeArchEndpointOrderTwentyHausdorffRectangle_cardinality :
    20 * 58 = 1160 := by
  norm_num

end

end RHTower
