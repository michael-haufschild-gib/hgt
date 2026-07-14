import GaloisForLFunctions.RHTower.XiThermalQuartetRelativeGapBound

/-!
# Cubic endpoint-charge bound for the Xi thermal orientation defect

For an off-line Xi copy, the endpoint cross charge is of order `gamma⁻²`, whereas the
transverse reciprocal-square energy is of order `gamma⁻⁶`.  The exact quartet height floor turns
this observation into an atomwise cubic inequality.  The four-copy charge cap and the exact
endpoint charge sum then give an absolute global defect bound below `1 / 150000`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The source-selected absolute cubic endpoint budget. -/
def xiThermalCubicEndpointBudget : ℝ :=
  (86 / 85 : ℝ) ^ 3 * xiEndpointCompletedCurvature ^ 3 / 16

/-- The exact source-dependent cubic endpoint budget. -/
def xiThermalExactCubicEndpointBudget : ℝ :=
  4 * (xiEndpointCompletedCurvature /
    (4 - xiEndpointCompletedCurvature)) ^ 3

/-- **Atomwise cubic endpoint-charge law.**  The transverse reciprocal-square energy of every
Xi copy is controlled by the cube of its endpoint cross charge.  On-line copies vanish.  For an
off-line copy, the quartet height floor gives `v > 85`; then
`e ≤ v⁻³ ≤ (86/85)^3 w^3`. -/
theorem xiThermalOrientationTerm_le_endpointCrossCharge_cube (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (86 / 85 : ℝ) ^ 3 * xiEndpointCrossCharge q ^ 3 := by
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hK : 0 ≤ (86 / 85 : ℝ) ^ 3 := by norm_num
    have hw : 0 ≤ xiEndpointCrossCharge q := by
      simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q
    rw [him, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg hK (pow_nonneg hw 3)
  · let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
    let v : ℝ := (q.1 : ℂ).im ^ 2
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hu : u ≤ 1 / 4 := by
      have hstrip := xi_divisor_support_re_mem_open_unit q.1
      dsimp [u]
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv : 85 < v := by
      simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hon
    have hv0 : 0 < v := by linarith
    have huv0 : 0 < u + v := add_pos_of_nonneg_of_pos hu0 hv0
    have hcore : 4 * u * v ^ 4 ≤ (u + v) ^ 4 := by
      have hcoef : 4 * u ≤ 1 := by linarith
      have hleft : 4 * u * v ^ 4 ≤ v ^ 4 := by
        calc
          4 * u * v ^ 4 ≤ 1 * v ^ 4 :=
            mul_le_mul_of_nonneg_right hcoef (pow_nonneg hv0.le 4)
          _ = v ^ 4 := one_mul _
      have hright : v ^ 4 ≤ (u + v) ^ 4 := by
        exact pow_le_pow_left₀ hv0.le (by linarith) 4
      exact hleft.trans hright
    have heInv :
        (xiZeroCopyReciprocalSquare q).im ^ 2 ≤ 1 / v ^ 3 := by
      rw [xiZeroCopyReciprocalSquare_im_formula]
      rw [show ((q.1 : ℂ).re - 1 / 2) ^ 2 = u by rfl,
        show (q.1 : ℂ).im ^ 2 = v by rfl, div_pow]
      rw [show (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 =
          4 * u * v by dsimp [u, v]; ring,
        show ((u + v) ^ 2) ^ 2 = (u + v) ^ 4 by ring]
      rw [div_le_div_iff₀ (pow_pos huv0 4) (pow_pos hv0 3)]
      ring_nf at hcore ⊢
      exact hcore
    have hcross : 1 / (v + 1) ≤ xiEndpointCrossCharge q := by
      simpa only [v, xiEndpointCrossCharge] using
        endpoint_cross_term_re_ge_inv_one_add_im_sq q
    have hbase : 1 / v ≤ (86 / 85 : ℝ) * (1 / (v + 1)) := by
      rw [show (86 / 85 : ℝ) * (1 / (v + 1)) =
          (86 / 85 : ℝ) / (v + 1) by ring]
      rw [div_le_div_iff₀ hv0 (by linarith : 0 < v + 1)]
      nlinarith
    have hInvCharge : 1 / v ≤
        (86 / 85 : ℝ) * xiEndpointCrossCharge q :=
      hbase.trans (mul_le_mul_of_nonneg_left hcross (by positivity))
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / v) hInvCharge 3
    calc
      (xiZeroCopyReciprocalSquare q).im ^ 2 ≤ 1 / v ^ 3 := heInv
      _ = (1 / v) ^ 3 := by
        simpa only [one_div] using (inv_pow v 3).symm
      _ ≤ ((86 / 85 : ℝ) * xiEndpointCrossCharge q) ^ 3 := hpow
      _ = (86 / 85 : ℝ) ^ 3 * xiEndpointCrossCharge q ^ 3 := by rw [mul_pow]

/-- **Exact atomwise cubic endpoint-charge law.**  Keeping the source curvature in the quartet
height floor replaces the rational factor `86 / 85` by the strictly sharper factor
`4 / (4 - C)`. -/
theorem xiThermalOrientationTerm_le_exactEndpointCrossCharge_cube (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 *
        xiEndpointCrossCharge q ^ 3 := by
  have hC0 : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hC4 : xiEndpointCompletedCurvature < 4 := by
    nlinarith [xiEndpointCompletedCurvature_lt_two_over_fortyThree]
  have hden : 0 < 4 - xiEndpointCompletedCurvature := sub_pos.mpr hC4
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hw : 0 ≤ xiEndpointCrossCharge q := by
      simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q
    rw [him, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (pow_nonneg (by positivity) 3) (pow_nonneg hw 3)
  · let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
    let v : ℝ := (q.1 : ℂ).im ^ 2
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hu : u ≤ 1 / 4 := by
      have hstrip := xi_divisor_support_re_mem_open_unit q.1
      dsimp [u]
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv : 85 < v := by
      simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hon
    have hv0 : 0 < v := by linarith
    have huv0 : 0 < u + v := add_pos_of_nonneg_of_pos hu0 hv0
    have hcore : 4 * u * v ^ 4 ≤ (u + v) ^ 4 := by
      have hcoef : 4 * u ≤ 1 := by linarith
      have hleft : 4 * u * v ^ 4 ≤ v ^ 4 := by
        calc
          4 * u * v ^ 4 ≤ 1 * v ^ 4 :=
            mul_le_mul_of_nonneg_right hcoef (pow_nonneg hv0.le 4)
          _ = v ^ 4 := one_mul _
      have hright : v ^ 4 ≤ (u + v) ^ 4 := by
        exact pow_le_pow_left₀ hv0.le (by linarith) 4
      exact hleft.trans hright
    have heInv :
        (xiZeroCopyReciprocalSquare q).im ^ 2 ≤ 1 / v ^ 3 := by
      rw [xiZeroCopyReciprocalSquare_im_formula]
      rw [show ((q.1 : ℂ).re - 1 / 2) ^ 2 = u by rfl,
        show (q.1 : ℂ).im ^ 2 = v by rfl, div_pow]
      rw [show (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 =
          4 * u * v by dsimp [u, v]; ring,
        show ((u + v) ^ 2) ^ 2 = (u + v) ^ 4 by ring]
      rw [div_le_div_iff₀ (pow_pos huv0 4) (pow_pos hv0 3)]
      ring_nf at hcore ⊢
      exact hcore
    have hcross : 1 / (v + 1) ≤ xiEndpointCrossCharge q := by
      simpa only [v, xiEndpointCrossCharge] using
        endpoint_cross_term_re_ge_inv_one_add_im_sq q
    have hfour : 4 ≤ xiEndpointCompletedCurvature * (v + 1) := by
      simpa only [v, add_comm] using
        four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hon
    have hbase : 1 / v ≤
        (4 / (4 - xiEndpointCompletedCurvature)) * (1 / (v + 1)) := by
      rw [show (4 / (4 - xiEndpointCompletedCurvature)) * (1 / (v + 1)) =
          (4 / (4 - xiEndpointCompletedCurvature)) / (v + 1) by ring]
      rw [div_le_div_iff₀ hv0 (by linarith : 0 < v + 1)]
      rw [show (4 / (4 - xiEndpointCompletedCurvature)) * v =
          (4 * v) / (4 - xiEndpointCompletedCurvature) by ring]
      rw [le_div_iff₀ hden]
      nlinarith
    have hInvCharge : 1 / v ≤
        (4 / (4 - xiEndpointCompletedCurvature)) * xiEndpointCrossCharge q :=
      hbase.trans (mul_le_mul_of_nonneg_left hcross (by positivity))
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / v) hInvCharge 3
    calc
      (xiZeroCopyReciprocalSquare q).im ^ 2 ≤ 1 / v ^ 3 := heInv
      _ = (1 / v) ^ 3 := by
        simpa only [one_div] using (inv_pow v 3).symm
      _ ≤ ((4 / (4 - xiEndpointCompletedCurvature)) *
          xiEndpointCrossCharge q) ^ 3 := hpow
      _ = (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 *
          xiEndpointCrossCharge q ^ 3 := by rw [mul_pow]

/-- The endpoint cross charges form an absolutely summable positive sequence. -/
theorem summable_xiEndpointCrossCharge : Summable xiEndpointCrossCharge := by
  exact Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm (fun q => by
    rw [Real.norm_eq_abs]
    exact abs_re_le_norm _)

/-- The total endpoint cross charge is the completed endpoint curvature. -/
theorem tsum_xiEndpointCrossCharge_eq_curvature :
    ∑' q : XiZeroCopy, xiEndpointCrossCharge q =
      xiEndpointCompletedCurvature := by
  calc
    ∑' q : XiZeroCopy, xiEndpointCrossCharge q =
        (∑' q : XiZeroCopy,
          xiRawReciprocalCoordinate q *
            (starRingEnd ℂ)
              (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := by
          rw [Complex.re_tsum summable_xiEndpointCrossTerm]
          rfl
    _ = xiEndpointCompletedCurvature := xiEndpointCompletedCurvature_eq_cross_re.symm

/-- The four-copy cap turns the cubic atomwise law into a summable linear charge majorant. -/
theorem xiThermalOrientationTerm_le_cubic_curvature_charge (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (86 / 85 : ℝ) ^ 3 *
        (xiEndpointCompletedCurvature / 4) ^ 2 *
          xiEndpointCrossCharge q := by
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg
      (mul_nonneg (by positivity) (sq_nonneg _))
      (by simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q)
  · have hw0 : 0 ≤ xiEndpointCrossCharge q := by
      simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q
    have hwle : xiEndpointCrossCharge q ≤
        xiEndpointCompletedCurvature / 4 := by
      have hfour := four_mul_xiEndpointCrossCharge_le_curvature_of_offLine q hon
      linarith
    have hwSq : xiEndpointCrossCharge q ^ 2 ≤
        (xiEndpointCompletedCurvature / 4) ^ 2 :=
      pow_le_pow_left₀ hw0 hwle 2
    have hwCube : xiEndpointCrossCharge q ^ 3 ≤
        (xiEndpointCompletedCurvature / 4) ^ 2 *
          xiEndpointCrossCharge q := by
      calc
        xiEndpointCrossCharge q ^ 3 =
            xiEndpointCrossCharge q ^ 2 * xiEndpointCrossCharge q := by ring
        _ ≤ (xiEndpointCompletedCurvature / 4) ^ 2 *
            xiEndpointCrossCharge q :=
          mul_le_mul_of_nonneg_right hwSq hw0
    have hscaled : (86 / 85 : ℝ) ^ 3 * xiEndpointCrossCharge q ^ 3 ≤
        (86 / 85 : ℝ) ^ 3 *
          ((xiEndpointCompletedCurvature / 4) ^ 2 *
            xiEndpointCrossCharge q) :=
      mul_le_mul_of_nonneg_left hwCube (by positivity)
    apply (xiThermalOrientationTerm_le_endpointCrossCharge_cube q).trans
    calc
      (86 / 85 : ℝ) ^ 3 * xiEndpointCrossCharge q ^ 3 ≤
          (86 / 85 : ℝ) ^ 3 *
            ((xiEndpointCompletedCurvature / 4) ^ 2 *
              xiEndpointCrossCharge q) := hscaled
      _ = (86 / 85 : ℝ) ^ 3 *
          (xiEndpointCompletedCurvature / 4) ^ 2 *
            xiEndpointCrossCharge q := by ring

/-- The exact quartet factor and four-copy charge cap give the sharp source-dependent linear
majorant used in the global cubic estimate. -/
theorem xiThermalOrientationTerm_le_exactCubicCurvatureCharge (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 *
        (xiEndpointCompletedCurvature / 4) ^ 2 *
          xiEndpointCrossCharge q := by
  have hC4 : xiEndpointCompletedCurvature < 4 := by
    nlinarith [xiEndpointCompletedCurvature_lt_two_over_fortyThree]
  have hfactor0 : 0 ≤ (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 :=
    pow_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr hC4.le)) 3
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg
      (mul_nonneg hfactor0 (sq_nonneg _))
      (by simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q)
  · have hw0 : 0 ≤ xiEndpointCrossCharge q := by
      simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q
    have hwle : xiEndpointCrossCharge q ≤
        xiEndpointCompletedCurvature / 4 := by
      have hfour := four_mul_xiEndpointCrossCharge_le_curvature_of_offLine q hon
      linarith
    have hwSq : xiEndpointCrossCharge q ^ 2 ≤
        (xiEndpointCompletedCurvature / 4) ^ 2 :=
      pow_le_pow_left₀ hw0 hwle 2
    have hwCube : xiEndpointCrossCharge q ^ 3 ≤
        (xiEndpointCompletedCurvature / 4) ^ 2 *
          xiEndpointCrossCharge q := by
      calc
        xiEndpointCrossCharge q ^ 3 =
            xiEndpointCrossCharge q ^ 2 * xiEndpointCrossCharge q := by ring
        _ ≤ (xiEndpointCompletedCurvature / 4) ^ 2 *
            xiEndpointCrossCharge q :=
          mul_le_mul_of_nonneg_right hwSq hw0
    apply (xiThermalOrientationTerm_le_exactEndpointCrossCharge_cube q).trans
    calc
      (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 *
          xiEndpointCrossCharge q ^ 3 ≤
        (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 *
          ((xiEndpointCompletedCurvature / 4) ^ 2 * xiEndpointCrossCharge q) :=
        mul_le_mul_of_nonneg_left hwCube hfactor0
      _ = (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 *
          (xiEndpointCompletedCurvature / 4) ^ 2 * xiEndpointCrossCharge q := by ring

/-- **Global cubic endpoint budget.**  The transverse thermal defect is bounded by the cube of
the exact completed endpoint source value. -/
theorem xiThermalOrientationEnergy_le_cubicEndpointBudget :
    xiThermalOrientationEnergy ≤ xiThermalCubicEndpointBudget := by
  let A : ℝ := (86 / 85 : ℝ) ^ 3 *
    (xiEndpointCompletedCurvature / 4) ^ 2
  have hscaled : Summable (fun q : XiZeroCopy => A * xiEndpointCrossCharge q) :=
    summable_xiEndpointCrossCharge.mul_left A
  have hle := summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q => by
      simpa only [A, mul_assoc] using
        xiThermalOrientationTerm_le_cubic_curvature_charge q)
    hscaled
  rw [← xiThermalOrientationEnergy] at hle
  calc
    xiThermalOrientationEnergy ≤
        ∑' q : XiZeroCopy, A * xiEndpointCrossCharge q := hle
    _ = A * (∑' q : XiZeroCopy, xiEndpointCrossCharge q) := tsum_mul_left
    _ = A * xiEndpointCompletedCurvature := by
      rw [tsum_xiEndpointCrossCharge_eq_curvature]
    _ = xiThermalCubicEndpointBudget := by
      dsimp [A, xiThermalCubicEndpointBudget]
      ring

/-- **Exact global cubic endpoint budget.**  The transverse thermal defect is bounded by the
source-dependent quartet expression `4 (C / (4 - C))³`. -/
theorem xiThermalOrientationEnergy_le_exactCubicEndpointBudget :
    xiThermalOrientationEnergy ≤ xiThermalExactCubicEndpointBudget := by
  let A : ℝ := (4 / (4 - xiEndpointCompletedCurvature)) ^ 3 *
    (xiEndpointCompletedCurvature / 4) ^ 2
  have hscaled : Summable (fun q : XiZeroCopy => A * xiEndpointCrossCharge q) :=
    summable_xiEndpointCrossCharge.mul_left A
  have hle := summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q => by
      simpa only [A, mul_assoc] using
        xiThermalOrientationTerm_le_exactCubicCurvatureCharge q)
    hscaled
  rw [← xiThermalOrientationEnergy] at hle
  have hden : 4 - xiEndpointCompletedCurvature ≠ 0 := by
    have hC4 : xiEndpointCompletedCurvature < 4 := by
      nlinarith [xiEndpointCompletedCurvature_lt_two_over_fortyThree]
    exact ne_of_gt (sub_pos.mpr hC4)
  calc
    xiThermalOrientationEnergy ≤
        ∑' q : XiZeroCopy, A * xiEndpointCrossCharge q := hle
    _ = A * (∑' q : XiZeroCopy, xiEndpointCrossCharge q) := tsum_mul_left
    _ = A * xiEndpointCompletedCurvature := by
      rw [tsum_xiEndpointCrossCharge_eq_curvature]
    _ = xiThermalExactCubicEndpointBudget := by
      dsimp [A, xiThermalExactCubicEndpointBudget]
      field_simp [hden]

/-- The exact source-dependent budget is strictly sharper than its rational cubic majorant. -/
theorem xiThermalExactCubicEndpointBudget_lt_cubicEndpointBudget :
    xiThermalExactCubicEndpointBudget < xiThermalCubicEndpointBudget := by
  let c : ℝ := xiEndpointCompletedCurvature
  let a : ℝ := 4 / (4 - c)
  let b : ℝ := 86 / 85
  have hc0 : 0 < c := by simpa only [c] using xiEndpointCompletedCurvature_pos
  have hc43 : c < 2 / 43 := by
    simpa only [c] using xiEndpointCompletedCurvature_lt_two_over_fortyThree
  have hden : 0 < 4 - c := by nlinarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hb0 : 0 < b := by norm_num [b]
  have hab : a < b := by
    dsimp [a, b]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hab3 : a ^ 3 < b ^ 3 := by
    have hsum : 0 < b ^ 2 + b * a + a ^ 2 := by positivity
    have hprod := mul_pos (sub_pos.mpr hab) hsum
    nlinarith [show (b - a) * (b ^ 2 + b * a + a ^ 2) = b ^ 3 - a ^ 3 by ring]
  have hscale : 0 < c ^ 3 / 16 := by positivity
  have hscaled := mul_lt_mul_of_pos_right hab3 hscale
  have hden0 : 4 - c ≠ 0 := ne_of_gt hden
  change 4 * (c / (4 - c)) ^ 3 < b ^ 3 * c ^ 3 / 16
  have hexact : 4 * (c / (4 - c)) ^ 3 = a ^ 3 * c ^ 3 / 16 := by
    dsimp [a]
    field_simp [hden0]
    ring
  rw [hexact]
  nlinarith

/-- The exact cubic endpoint budget is below `1 / 150000`. -/
theorem xiThermalCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand :
    xiThermalCubicEndpointBudget < 1 / 150000 := by
  let c : ℝ := xiEndpointCompletedCurvature
  let c0 : ℝ := 93 / 2000
  have hc0 : 0 < c := by simpa only [c] using xiEndpointCompletedCurvature_pos
  have hc : c < c0 := by
    simpa only [c, c0] using
      xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand
  have hc03 : c ^ 3 < c0 ^ 3 := by
    nlinarith [mul_pos (sub_pos.mpr hc) (add_pos hc0 (by positivity : 0 < c0)),
      mul_pos (sub_pos.mpr hc)
        (by nlinarith : 0 < c ^ 2 + c * c0 + c0 ^ 2)]
  change (86 / 85 : ℝ) ^ 3 * c ^ 3 / 16 < 1 / 150000
  have hK : 0 < (86 / 85 : ℝ) ^ 3 / 16 := by positivity
  have hlt := mul_lt_mul_of_pos_left hc03 hK
  have hrat : (86 / 85 : ℝ) ^ 3 * c0 ^ 3 / 16 < 1 / 150000 := by
    norm_num [c0]
  nlinarith

/-- The exact source-dependent cubic endpoint budget is below `1 / 150000`. -/
theorem xiThermalExactCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand :
    xiThermalExactCubicEndpointBudget < 1 / 150000 :=
  xiThermalExactCubicEndpointBudget_lt_cubicEndpointBudget.trans
    xiThermalCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand

/-- **Absolute transverse-energy bound.** -/
theorem xiThermalOrientationEnergy_lt_one_over_oneHundredFiftyThousand :
    xiThermalOrientationEnergy < 1 / 150000 :=
  xiThermalOrientationEnergy_le_exactCubicEndpointBudget.trans_lt
    xiThermalExactCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand

/-- The thermal/source gap is exactly the transverse orientation energy. -/
theorem xiThermalSecondMoment_sub_source_eq_orientationEnergy :
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 =
      xiThermalOrientationEnergy := by
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

/-- **Absolute source-gap interval.**  The positive thermal second moment exceeds the exact
prime--Gamma source value by a nonnegative quantity below `1 / 150000`. -/
theorem xiThermalSecondMoment_source_absoluteGap :
    0 ≤ xiThermalSecondMoment - normalizedPrimeArchMoment 1 ∧
      xiThermalSecondMoment - normalizedPrimeArchMoment 1 < 1 / 150000 := by
  rw [xiThermalSecondMoment_sub_source_eq_orientationEnergy]
  exact ⟨xiThermalOrientationEnergy_nonneg,
    xiThermalOrientationEnergy_lt_one_over_oneHundredFiftyThousand⟩

end

end RHTower
