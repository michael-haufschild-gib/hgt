import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenSourceMoment
import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovEquivalence

/-!
# A strict relative bound for the Xi thermal orientation gap

The completed endpoint source gives more than positivity of the reciprocal-square thermal nodes.
An elementary strengthening of its explicit value bound forces every Xi zero above squared height
`2`.  Combining that gap with the open critical strip bounds the transverse part of every
reciprocal-square coordinate by `32/49` of its real square.  Summation produces a two-sided
source/thermal estimate and identifies the prime--archimedean source moment with an explicit
quadratic functional of the theta Born/Witten ground states.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A stronger elementary lower bound for the logarithmic term in the completed endpoint value. -/
lemma seven_div_three_lt_log_four_mul_pi :
    7 / 3 < Real.log (4 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have hexpTwo : Real.exp 2 < 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h : Real.exp 1 < (2.72 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    nlinarith [Real.exp_pos 1]
  have hexpThird : Real.exp (1 / 3 : ℝ) ≤ 3 / 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [show (7 / 3 : ℝ) = 2 + 1 / 3 by norm_num, Real.exp_add]
  calc
    Real.exp 2 * Real.exp (1 / 3) < 8 * Real.exp (1 / 3) :=
      mul_lt_mul_of_pos_right hexpTwo (Real.exp_pos _)
    _ ≤ 8 * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hexpThird (by norm_num)
    _ < 4 * Real.pi := by nlinarith [Real.pi_gt_three]

/-- The completed endpoint curvature is already below one third. -/
theorem xiEndpointCompletedCurvature_lt_one_third :
    xiEndpointCompletedCurvature < 1 / 3 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log]
  nlinarith [Real.eulerMascheroniConstant_lt_two_thirds,
    seven_div_three_lt_log_four_mul_pi]

/-- The sharpened endpoint source bound forces every Xi multiplicity copy above squared height
`2`. -/
theorem xiZeroCopy_two_lt_im_sq (q : XiZeroCopy) :
    2 < (q.1 : ℂ).im ^ 2 := by
  have hCpos := xiEndpointCompletedCurvature_pos
  have hCinv : 3 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [xiEndpointCompletedCurvature_lt_one_third]
  have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  linarith

/-- Real part of the centered reciprocal-square coordinate in horizontal/vertical zero
coordinates. -/
theorem xiZeroCopyReciprocalSquare_re_formula (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).re =
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2 := by
  rw [xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf]
  simp only [Complex.neg_re, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [show Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)) =
      ((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2 by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero]
    ring]
  have hden : ((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  field_simp [hden]
  ring

/-- Imaginary part of the centered reciprocal-square coordinate in horizontal/vertical zero
coordinates. -/
theorem xiZeroCopyReciprocalSquare_im_formula (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im =
      2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2 := by
  rw [xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf]
  simp only [Complex.neg_im, pow_two, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [show Complex.normSq ((q.1 : ℂ) - ((1 / 2 : ℝ) : ℂ)) =
      ((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2 by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero]
    ring]
  have hden : ((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  field_simp [hden]
  ring

/-- **Atomwise relative orientation bound.**  At every Xi zero, the squared transverse part of
the reciprocal-square coordinate is at most `32/49` of the squared positive thermal node. -/
theorem xiThermalOrientationTerm_le_thirtyTwo_over_fortyNine_node_sq
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (32 / 49 : ℝ) * xiThermalNode q ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let D : ℝ := (u + v) ^ 2
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u < 1 / 4 := by
    dsimp [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : 2 < v := by simpa only [v] using xiZeroCopy_two_lt_im_sq q
  have hD : 0 < D := by dsimp [D]; positivity
  rw [xiThermalNode, xiZeroCopyReciprocalSquare_re_formula,
    xiZeroCopyReciprocalSquare_im_formula]
  change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2 ≤
    (32 / 49 : ℝ) *
      (((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2
  rw [show ((q.1 : ℂ).re - 1 / 2) ^ 2 = u by rfl,
    show (q.1 : ℂ).im ^ 2 = v by rfl,
    show (u + v) ^ 2 = D by rfl]
  rw [div_pow, div_pow]
  rw [show (32 / 49 : ℝ) * ((v - u) ^ 2 / D ^ 2) =
      ((32 / 49 : ℝ) * (v - u) ^ 2) / D ^ 2 by ring]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2
  have hvEightU : 0 ≤ v - 8 * u := by linarith
  have hvUOverEight : 0 ≤ v - u / 8 := by linarith
  have hfactor : 0 ≤ (v - 8 * u) * (v - u / 8) :=
    mul_nonneg hvEightU hvUOverEight
  have hcore : 4 * u * v ≤ (32 / 49 : ℝ) * (v - u) ^ 2 := by
    nlinarith [hfactor]
  calc
    (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 = 4 * u * v := by
      dsimp [u, v]
      ring
    _ ≤ (32 / 49 : ℝ) * (v - u) ^ 2 := hcore

lemma four_mul_u_mul_v_le_boundary_ratio
    {a u v : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4)
    (ha : 1 / 4 < a) (hv : a ≤ v) :
    4 * u * v ≤ (a / (a - 1 / 4) ^ 2) * (v - u) ^ 2 := by
  have hau : 0 < a - u := by linarith
  have hav : 0 < v - u := by linarith
  have hab : 0 < a - 1 / 4 := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hmonoVCore : v * (a - u) ^ 2 ≤ a * (v - u) ^ 2 := by
    have h1 : 0 ≤ v - a := sub_nonneg.mpr hv
    have h2 : 0 ≤ a * v - u ^ 2 := by
      have huv : u ≤ a := hu.trans ha.le
      have haa : a ^ 2 ≤ a * v := by
        nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hv)]
      nlinarith [mul_nonneg (sub_nonneg.mpr huv) (add_nonneg ha0 hu0)]
    nlinarith [mul_nonneg h1 h2]
  have hmonoV :
      4 * u * v / (v - u) ^ 2 ≤ 4 * u * a / (a - u) ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hav) (sq_pos_of_pos hau)]
    calc
      4 * u * v * (a - u) ^ 2 = (4 * u) * (v * (a - u) ^ 2) := by ring
      _ ≤ (4 * u) * (a * (v - u) ^ 2) :=
        mul_le_mul_of_nonneg_left hmonoVCore (by positivity)
      _ = 4 * u * a * (v - u) ^ 2 := by ring
  have hmonoUCore : u * (a - 1 / 4) ^ 2 ≤ (1 / 4 : ℝ) * (a - u) ^ 2 := by
    have h1 : 0 ≤ (1 / 4 : ℝ) - u := sub_nonneg.mpr hu
    have h2 : 0 ≤ a ^ 2 - (1 / 4 : ℝ) * u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hu.trans ha.le))
        (add_nonneg ha0 hu0)]
    nlinarith [mul_nonneg h1 h2]
  have hmonoU :
      4 * u * a / (a - u) ^ 2 ≤ a / (a - 1 / 4) ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hau) (sq_pos_of_pos hab)]
    have hscaled := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ha0)
      (sub_nonneg.mpr hmonoUCore)
    nlinarith
  have hratio := hmonoV.trans hmonoU
  rw [div_le_iff₀ (sq_pos_of_pos hav)] at hratio
  exact hratio

/-- The exact relative orientation factor selected by the completed endpoint source. -/
def xiThermalRelativeOrientationFactor : ℝ :=
  16 * xiEndpointCompletedCurvature * (1 - xiEndpointCompletedCurvature) /
    (4 - 5 * xiEndpointCompletedCurvature) ^ 2

theorem xiThermalRelativeOrientationFactor_eq_boundaryRatio :
    xiThermalRelativeOrientationFactor =
      ((1 - xiEndpointCompletedCurvature) / xiEndpointCompletedCurvature) /
        ((1 - xiEndpointCompletedCurvature) / xiEndpointCompletedCurvature - 1 / 4) ^ 2 := by
  have hCne := xiEndpointCompletedCurvature_pos.ne'
  unfold xiThermalRelativeOrientationFactor
  field_simp [hCne]
  ring

/-- Exact atomwise source-controlled orientation estimate. -/
theorem xiThermalOrientationTerm_le_relativeFactor_node_sq (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      xiThermalRelativeOrientationFactor * xiThermalNode q ^ 2 := by
  let c : ℝ := xiEndpointCompletedCurvature
  let a : ℝ := (1 - c) / c
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let D : ℝ := (u + v) ^ 2
  have hc0 : 0 < c := by simpa only [c] using xiEndpointCompletedCurvature_pos
  have hc : c < 1 / 3 := by
    simpa only [c] using xiEndpointCompletedCurvature_lt_one_third
  have ha : 1 / 4 < a := by
    dsimp [a]
    rw [lt_div_iff₀ hc0]
    nlinarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ 1 / 4 := by
    dsimp [u]
    nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
  have hv : a ≤ v := by
    have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
    dsimp [a, c, v]
    rw [show (1 - xiEndpointCompletedCurvature) /
        xiEndpointCompletedCurvature =
          1 / xiEndpointCompletedCurvature - 1 by
      field_simp [xiEndpointCompletedCurvature_pos.ne']]
    exact hheight
  have hv0 : 0 < v := by
    dsimp [v]
    exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hratio := four_mul_u_mul_v_le_boundary_ratio hu0 hu ha hv
  rw [xiThermalNode, xiZeroCopyReciprocalSquare_re_formula,
    xiZeroCopyReciprocalSquare_im_formula]
  change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2 ≤
    xiThermalRelativeOrientationFactor *
      (((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2
  rw [show ((q.1 : ℂ).re - 1 / 2) ^ 2 = u by rfl,
    show (q.1 : ℂ).im ^ 2 = v by rfl,
    show (u + v) ^ 2 = D by rfl,
    xiThermalRelativeOrientationFactor_eq_boundaryRatio]
  change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im / D) ^ 2 ≤
    (a / (a - 1 / 4) ^ 2) * ((v - u) / D) ^ 2
  rw [div_pow, div_pow]
  rw [show (a / (a - 1 / 4) ^ 2) * ((v - u) ^ 2 / D ^ 2) =
      ((a / (a - 1 / 4) ^ 2) * (v - u) ^ 2) / D ^ 2 by ring]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2
  calc
    (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 = 4 * u * v := by
      dsimp [u, v]
      ring
    _ ≤ (a / (a - 1 / 4) ^ 2) * (v - u) ^ 2 := hratio

theorem xiThermalRelativeOrientationFactor_nonneg :
    0 ≤ xiThermalRelativeOrientationFactor := by
  unfold xiThermalRelativeOrientationFactor
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) xiEndpointCompletedCurvature_pos.le)
      (sub_nonneg.mpr xiEndpointCompletedCurvature_lt_one.le))
    (sq_nonneg _)

/-- The exact relative factor is already strictly smaller than the rational fallback `32/49`. -/
theorem xiThermalRelativeOrientationFactor_lt_thirtyTwo_over_fortyNine :
    xiThermalRelativeOrientationFactor < 32 / 49 := by
  let c : ℝ := xiEndpointCompletedCurvature
  have hc0 : 0 < c := by simpa only [c] using xiEndpointCompletedCurvature_pos
  have hc : c < 1 / 3 := by
    simpa only [c] using xiEndpointCompletedCurvature_lt_one_third
  have hden : 0 < 4 - 5 * c := by linarith
  have hprod : 0 < (1 / 3 - c) * (32 / 33 - c) := by
    exact mul_pos (sub_pos.mpr hc) (by nlinarith)
  unfold xiThermalRelativeOrientationFactor
  change 16 * c * (1 - c) / (4 - 5 * c) ^ 2 < 32 / 49
  rw [div_lt_iff₀ (sq_pos_of_pos hden)]
  nlinarith

set_option maxRecDepth 1000000 in
/-- A certified decimal-free upper bound for Euler's constant, obtained from the decreasing
Euler--Mascheroni sequence at the factorable index `3125 = 5^5`. -/
lemma eulerMascheroniConstant_lt_twoThousandEightHundredEightySeven_over_fiveThousand :
    Real.eulerMascheroniConstant < 2887 / 5000 := by
  refine (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 3125).trans ?_
  rw [Real.eulerMascheroniSeq']
  norm_num only [if_false, Nat.reduceEqDiff, Nat.cast_ofNat]
  rw [show (3125 : ℝ) = 5 ^ 5 by norm_num, Real.log_pow]
  have h := Real.log_five_gt_d9
  norm_num [harmonic] at *
  linarith

/-- A certified lower bound for the archimedean logarithm.  The smooth rational number
`5^26 / (2^6 * 3^32)` lies below `4 * pi`, and the standard rigorous bounds for the logarithms
of `2`, `3`, and `5` evaluate its logarithm. -/
lemma twoThousandFiveHundredThirtyNine_over_thousand_lt_log_four_mul_pi :
    25309 / 10000 < Real.log (4 * Real.pi) := by
  let v : ℝ := 5 ^ 26 / (2 ^ 6 * 3 ^ 32)
  have hvpos : 0 < v := by
    dsimp [v]
    positivity
  have hvpi : v < 4 * Real.pi := by
    dsimp [v]
    nlinarith [Real.pi_gt_d20]
  have hlogv : 25309 / 10000 < Real.log v := by
    dsimp [v]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    nlinarith [Real.log_five_gt_d9, Real.log_two_lt_d9,
      Real.log_three_lt_d9]
  exact hlogv.trans (Real.log_lt_log hvpos hvpi)

/-- The exact completed endpoint curvature is below `2/43`. -/
theorem xiEndpointCompletedCurvature_lt_two_over_fortyThree :
    xiEndpointCompletedCurvature < 2 / 43 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log]
  nlinarith
    [eulerMascheroniConstant_lt_twoThousandEightHundredEightySeven_over_fiveThousand,
      twoThousandFiveHundredThirtyNine_over_thousand_lt_log_four_mul_pi]

/-- The exact source-selected transverse factor is below five percent. -/
theorem xiThermalRelativeOrientationFactor_lt_one_twentieth :
    xiThermalRelativeOrientationFactor < 1 / 20 := by
  let c : ℝ := xiEndpointCompletedCurvature
  have hc0 : 0 < c := by simpa only [c] using xiEndpointCompletedCurvature_pos
  have hc : c < 2 / 43 := by
    simpa only [c] using xiEndpointCompletedCurvature_lt_two_over_fortyThree
  have hden : 0 < 4 - 5 * c := by linarith
  unfold xiThermalRelativeOrientationFactor
  change 16 * c * (1 - c) / (4 - 5 * c) ^ 2 < 1 / 20
  rw [div_lt_iff₀ (sq_pos_of_pos hden)]
  nlinarith [mul_pos (sub_pos.mpr hc) (by nlinarith : 0 < 82 / 21 - c)]

theorem xiThermalRelativeOrientationFactor_lt_one :
    xiThermalRelativeOrientationFactor < 1 :=
  xiThermalRelativeOrientationFactor_lt_one_twentieth.trans (by norm_num)

/-- The global orientation energy obeys the exact endpoint-source relative factor. -/
theorem xiThermalOrientationEnergy_le_relativeFactor_secondMoment :
    xiThermalOrientationEnergy ≤
      xiThermalRelativeOrientationFactor * xiThermalSecondMoment := by
  rw [xiThermalOrientationEnergy, xiThermalSecondMoment, ← tsum_mul_left]
  exact summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q => xiThermalOrientationTerm_le_relativeFactor_node_sq q)
    (summable_xiThermalNode_sq.mul_left xiThermalRelativeOrientationFactor)

/-- Exact source retention after subtracting the transverse thermal channel. -/
theorem relativeFactor_complement_mul_thermalSecondMoment_le_source :
    (1 - xiThermalRelativeOrientationFactor) * xiThermalSecondMoment ≤
      normalizedPrimeArchMoment 1 := by
  have hgap := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  have hbound := xiThermalOrientationEnergy_le_relativeFactor_secondMoment
  nlinarith

/-- **Exact two-sided thermal/source estimate.** -/
theorem xiThermalSecondMoment_le_source_div_relativeFactorComplement :
    xiThermalSecondMoment ≤
      normalizedPrimeArchMoment 1 / (1 - xiThermalRelativeOrientationFactor) := by
  rw [le_div_iff₀ (sub_pos.mpr xiThermalRelativeOrientationFactor_lt_one)]
  simpa only [mul_comm] using
    relativeFactor_complement_mul_thermalSecondMoment_le_source

/-- **Global relative orientation bound.**  The transverse thermal energy is a strict universal
fraction of the positive thermal second moment. -/
theorem xiThermalOrientationEnergy_le_thirtyTwo_over_fortyNine_secondMoment :
    xiThermalOrientationEnergy ≤ (32 / 49 : ℝ) * xiThermalSecondMoment := by
  rw [xiThermalOrientationEnergy, xiThermalSecondMoment, ← tsum_mul_left]
  exact summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q => xiThermalOrientationTerm_le_thirtyTwo_over_fortyNine_node_sq q)
    (summable_xiThermalNode_sq.mul_left (32 / 49 : ℝ))

/-- The prime--archimedean source captures at least `17/49` of the thermal second moment. -/
theorem seventeen_over_fortyNine_thermalSecondMoment_le_source :
    (17 / 49 : ℝ) * xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1 := by
  have hgap := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  have hbound := xiThermalOrientationEnergy_le_thirtyTwo_over_fortyNine_secondMoment
  nlinarith

/-- **Two-sided thermal/source estimate.**  The missing reverse endpoint is approached
unconditionally up to the explicit factor `49/17`. -/
theorem xiThermalSecondMoment_le_fortyNine_over_seventeen_source :
    xiThermalSecondMoment ≤ (49 / 17 : ℝ) * normalizedPrimeArchMoment 1 := by
  have h := seventeen_over_fortyNine_thermalSecondMoment_le_source
  nlinarith

/-- The canonical positive thermal second moment is strictly positive. -/
theorem xiThermalSecondMoment_pos : 0 < xiThermalSecondMoment := by
  obtain ⟨z, hz⟩ := xiDivisorSupport_infinite.nonempty
  let rho : XiDivisorSupport := ⟨z, hz⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by omega
    exact ⟨rho, ⟨0, hn⟩⟩
  have hterm := summable_xiThermalNode_sq.le_tsum q
    (fun j _ => sq_nonneg (xiThermalNode j))
  rw [← xiThermalSecondMoment] at hterm
  exact (sq_pos_of_pos (xiThermalNode_pos q)).trans_le hterm

/-- **Five-percent transverse-energy theorem.**  The global off-line orientation energy is
strictly less than one twentieth of the positive thermal second moment. -/
theorem xiThermalOrientationEnergy_lt_one_twentieth_secondMoment :
    xiThermalOrientationEnergy < (1 / 20 : ℝ) * xiThermalSecondMoment := by
  exact xiThermalOrientationEnergy_le_relativeFactor_secondMoment.trans_lt
    (mul_lt_mul_of_pos_right xiThermalRelativeOrientationFactor_lt_one_twentieth
      xiThermalSecondMoment_pos)

/-- The first nontrivial normalized prime--archimedean source moment is strictly positive. -/
theorem normalizedPrimeArchMoment_one_pos : 0 < normalizedPrimeArchMoment 1 := by
  have hlower := seventeen_over_fortyNine_thermalSecondMoment_le_source
  nlinarith [xiThermalSecondMoment_pos]

/-- The arithmetic source retains strictly more than nineteen twentieths of the positive thermal
second moment. -/
theorem nineteen_over_twenty_thermalSecondMoment_lt_source :
    (19 / 20 : ℝ) * xiThermalSecondMoment < normalizedPrimeArchMoment 1 := by
  have hgap := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  have horientation := xiThermalOrientationEnergy_lt_one_twentieth_secondMoment
  nlinarith

/-- **Twenty-over-nineteen thermal/source theorem.**  The positive thermal moment lies in a
strict interval whose multiplicative width is less than `20/19`. -/
theorem xiThermalSecondMoment_lt_twenty_over_nineteen_source :
    xiThermalSecondMoment < (20 / 19 : ℝ) * normalizedPrimeArchMoment 1 := by
  nlinarith [nineteen_over_twenty_thermalSecondMoment_lt_source]

/-- The exact source-dependent inflation bound is strictly sharper than the rational fallback. -/
theorem source_div_relativeFactorComplement_lt_fortyNine_over_seventeen_source :
    normalizedPrimeArchMoment 1 /
        (1 - xiThermalRelativeOrientationFactor) <
      (49 / 17 : ℝ) * normalizedPrimeArchMoment 1 := by
  have hk := xiThermalRelativeOrientationFactor_lt_thirtyTwo_over_fortyNine
  have hden : 0 < 1 - xiThermalRelativeOrientationFactor := by linarith
  have hfactor :
      0 < (49 / 17 : ℝ) * (1 - xiThermalRelativeOrientationFactor) - 1 := by
    nlinarith
  rw [div_lt_iff₀ hden]
  nlinarith [mul_pos normalizedPrimeArchMoment_one_pos hfactor]

/-- The exact source-dependent inflation factor is strictly smaller than `20/19`. -/
theorem source_div_relativeFactorComplement_lt_twenty_over_nineteen_source :
    normalizedPrimeArchMoment 1 /
        (1 - xiThermalRelativeOrientationFactor) <
      (20 / 19 : ℝ) * normalizedPrimeArchMoment 1 := by
  have hk := xiThermalRelativeOrientationFactor_lt_one_twentieth
  have hden : 0 < 1 - xiThermalRelativeOrientationFactor := by linarith
  have hfactor :
      0 < (20 / 19 : ℝ) * (1 - xiThermalRelativeOrientationFactor) - 1 := by
    nlinarith
  rw [div_lt_iff₀ hden]
  nlinarith [mul_pos normalizedPrimeArchMoment_one_pos hfactor]

/-- The exact thermal gap identity with the source side written entirely as a quadratic
Born/Witten ground-state functional. -/
theorem xiThermalSecondMoment_sub_orientationEnergy_eq_bornWittenSource :
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact xiThermalSecondMoment_sub_orientationEnergy_eq_source

/-- The quadratic Born/Witten source value is strictly positive. -/
theorem thetaCuspBornWittenQuadraticSource_pos :
    0 < thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact normalizedPrimeArchMoment_one_pos

/-- Two-sided quantitative incidence between the theta Born/Witten source and the Xi thermal
divisor. -/
theorem thetaCuspBornWittenQuadraticSource_le_thermalSecondMoment :
    thetaCuspBornWittenQuadraticSource ≤ xiThermalSecondMoment := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact normalizedPrimeArchMoment_one_le_xiThermalSecondMoment

theorem xiThermalSecondMoment_le_fortyNine_over_seventeen_bornWittenSource :
    xiThermalSecondMoment ≤
      (49 / 17 : ℝ) * thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact xiThermalSecondMoment_le_fortyNine_over_seventeen_source

theorem nineteen_over_twenty_thermalSecondMoment_lt_bornWittenSource :
    (19 / 20 : ℝ) * xiThermalSecondMoment <
      thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact nineteen_over_twenty_thermalSecondMoment_lt_source

theorem xiThermalSecondMoment_lt_twenty_over_nineteen_bornWittenSource :
    xiThermalSecondMoment <
      (20 / 19 : ℝ) * thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact xiThermalSecondMoment_lt_twenty_over_nineteen_source

theorem relativeFactor_complement_mul_thermalSecondMoment_le_bornWittenSource :
    (1 - xiThermalRelativeOrientationFactor) * xiThermalSecondMoment ≤
      thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact relativeFactor_complement_mul_thermalSecondMoment_le_source

theorem xiThermalSecondMoment_le_bornWittenSource_div_relativeFactorComplement :
    xiThermalSecondMoment ≤
      thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact xiThermalSecondMoment_le_source_div_relativeFactorComplement

theorem bornWittenSource_div_relativeFactorComplement_lt_fortyNine_over_seventeen :
    thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) <
      (49 / 17 : ℝ) * thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact source_div_relativeFactorComplement_lt_fortyNine_over_seventeen_source

theorem bornWittenSource_div_relativeFactorComplement_lt_twenty_over_nineteen :
    thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) <
      (20 / 19 : ℝ) * thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact source_div_relativeFactorComplement_lt_twenty_over_nineteen_source

/-- Saturation of the Born/Witten-to-thermal comparison is exactly RH. -/
theorem xiThermalSecondMoment_eq_bornWittenSource_iff_rh :
    xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
      RiemannHypothesis := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact xiThermalSecondMoment_eq_source_iff_rh

/-- Reversing the unconditional Born/Witten source lower bound is exactly RH. -/
theorem xiThermalSecondMoment_le_bornWittenSource_iff_rh :
    xiThermalSecondMoment ≤ thetaCuspBornWittenQuadraticSource ↔
      RiemannHypothesis := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact xiThermalSecondMoment_le_source_iff_rh

/-- Convergence of the explicit finite KMS second moments to the theta Born/Witten source value
is exactly RH. -/
theorem tendsto_xiThermalTruncation_one_bornWittenSource_iff_rh :
    Tendsto (fun N => xiThermalTruncation N 1) atTop
      (nhds thetaCuspBornWittenQuadraticSource) ↔ RiemannHypothesis := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact tendsto_xiThermalTruncation_one_iff_rh

/-- **Born/Witten--thermal quantitative master law.**  The theta source is a countable sum of
exact pure Witten ground-state densities with a uniform atomwise curvature certificate.  Its
first normalized trace value is the displayed quadratic pure-state moment functional.  The
finite KMS divisor systems converge to a positive thermal value lying in the explicit interval
`[source, (49/17) source]`; the lower endpoint is attained exactly on RH. -/
theorem xiBornWittenThermalQuantitativeMaster :
    (∀ x : ℝ, 0 ≤ x →
      thetaCuspFullSource x =
        Real.pi * ∑' n : ℕ, thetaCuspBornWittenAmplitude n x ^ 2) ∧
    (∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x →
      thetaCuspSourceTerm x n =
          Real.pi * thetaCuspBornWittenAmplitude n x ^ 2 ∧
      deriv (thetaCuspBornWittenAmplitude n) x +
          thetaCuspBornWittenSuperpotential n x *
            thetaCuspBornWittenAmplitude n x = 0 ∧
      4 * Real.pi * (n : ℝ) ^ 2 ≤
          thetaCuspBornWittenLogCurvature n x) ∧
    normalizedPrimeArchMoment 1 = thetaCuspBornWittenQuadraticSource ∧
    0 < thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment - xiThermalOrientationEnergy =
      thetaCuspBornWittenQuadraticSource ∧
    xiThermalRelativeOrientationFactor < 1 / 20 ∧
    xiThermalRelativeOrientationFactor < 32 / 49 ∧
    xiThermalOrientationEnergy ≤
      xiThermalRelativeOrientationFactor * xiThermalSecondMoment ∧
    (1 - xiThermalRelativeOrientationFactor) * xiThermalSecondMoment ≤
      thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment ≤
      thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) ∧
    thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) <
      (20 / 19 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    thetaCuspBornWittenQuadraticSource /
        (1 - xiThermalRelativeOrientationFactor) <
      (49 / 17 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    xiThermalOrientationEnergy <
      (1 / 20 : ℝ) * xiThermalSecondMoment ∧
    xiThermalOrientationEnergy ≤
      (32 / 49 : ℝ) * xiThermalSecondMoment ∧
    thetaCuspBornWittenQuadraticSource ≤ xiThermalSecondMoment ∧
    xiThermalSecondMoment <
      (20 / 19 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    xiThermalSecondMoment ≤
      (49 / 17 : ℝ) * thetaCuspBornWittenQuadraticSource ∧
    (xiThermalSecondMoment = thetaCuspBornWittenQuadraticSource ↔
      RiemannHypothesis) ∧
    (Tendsto (fun N => xiThermalTruncation N 1) atTop
      (nhds thetaCuspBornWittenQuadraticSource) ↔ RiemannHypothesis) := by
  refine ⟨fun x hx => thetaCuspFullSource_eq_pi_mul_tsum_bornWittenAmplitude_sq hx,
    ?_, normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource,
    thetaCuspBornWittenQuadraticSource_pos,
    xiThermalSecondMoment_sub_orientationEnergy_eq_bornWittenSource,
    xiThermalRelativeOrientationFactor_lt_one_twentieth,
    xiThermalRelativeOrientationFactor_lt_thirtyTwo_over_fortyNine,
    xiThermalOrientationEnergy_le_relativeFactor_secondMoment,
    relativeFactor_complement_mul_thermalSecondMoment_le_bornWittenSource,
    xiThermalSecondMoment_le_bornWittenSource_div_relativeFactorComplement,
    bornWittenSource_div_relativeFactorComplement_lt_twenty_over_nineteen,
    bornWittenSource_div_relativeFactorComplement_lt_fortyNine_over_seventeen,
    xiThermalOrientationEnergy_lt_one_twentieth_secondMoment,
    xiThermalOrientationEnergy_le_thirtyTwo_over_fortyNine_secondMoment,
    thetaCuspBornWittenQuadraticSource_le_thermalSecondMoment,
    xiThermalSecondMoment_lt_twenty_over_nineteen_bornWittenSource,
    xiThermalSecondMoment_le_fortyNine_over_seventeen_bornWittenSource,
    xiThermalSecondMoment_eq_bornWittenSource_iff_rh,
    tendsto_xiThermalTruncation_one_bornWittenSource_iff_rh⟩
  intro n hn x hx
  exact ⟨thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hx,
    thetaCuspBornWitten_supercharge_zero hn hx,
    thetaCuspBornWittenLogCurvature_floor hn hx⟩

end

end RHTower
