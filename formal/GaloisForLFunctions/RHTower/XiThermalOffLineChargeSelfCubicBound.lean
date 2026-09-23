import GaloisForLFunctions.RHTower.XiThermalQuartetCubicChargeBound

/-!
# Self-localized off-line endpoint charge for the Xi thermal defect

The completed endpoint curvature contains both critical-line and off-line cross charge.  This
module isolates the off-line part.  Every FE--Schwarz quartet of an off-line copy remains inside
that sector, so the quartet height and cubic thermal estimates can be paid from the off-line
charge alone.  The resulting budget vanishes exactly on RH.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The multiplicity-exact off-critical part of the Xi divisor. -/
def xiEndpointOffLineSet : Set XiZeroCopy :=
  {q | (q.1 : ℂ).re ≠ 1 / 2}

/-- One endpoint cross charge, retained only off the critical line. -/
def xiEndpointOffLineChargeTerm : XiZeroCopy → ℝ :=
  xiEndpointOffLineSet.indicator xiEndpointCrossCharge

/-- The total endpoint cross charge carried by off-line Xi copies. -/
def xiEndpointOffLineCharge : ℝ :=
  ∑' q : XiZeroCopy, xiEndpointOffLineChargeTerm q

/-- The exact self-localized cubic budget selected by the off-line endpoint charge. -/
def xiThermalOffLineChargeCubicBudget : ℝ :=
  4 * (xiEndpointOffLineCharge / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ)

theorem xiEndpointOffLineSet_lineConj (q : XiZeroCopy)
    (h : (q.1 : ℂ).re ≠ 1 / 2) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).re ≠ 1 / 2 := by
  change (1 - (starRingEnd ℂ) (q.1 : ℂ)).re ≠ 1 / 2
  simp only [sub_re, one_re, conj_re]
  intro heq
  apply h
  linarith

theorem xiEndpointOffLineSet_conj (q : XiZeroCopy)
    (h : (q.1 : ℂ).re ≠ 1 / 2) :
    ((xiZeroCopyConjEquiv q).1 : ℂ).re ≠ 1 / 2 := by
  change ((starRingEnd ℂ) (q.1 : ℂ)).re ≠ 1 / 2
  simpa only [conj_re] using h

theorem xiEndpointOffLineChargeTerm_eq (q : XiZeroCopy)
    (h : (q.1 : ℂ).re ≠ 1 / 2) :
    xiEndpointOffLineChargeTerm q = xiEndpointCrossCharge q := by
  rw [xiEndpointOffLineChargeTerm, Set.indicator_of_mem]
  exact h

theorem xiEndpointOffLineChargeTerm_eq_zero (q : XiZeroCopy)
    (h : (q.1 : ℂ).re = 1 / 2) :
    xiEndpointOffLineChargeTerm q = 0 := by
  rw [xiEndpointOffLineChargeTerm, Set.indicator_of_notMem]
  intro hoff
  exact hoff h

theorem summable_xiEndpointOffLineChargeTerm :
    Summable xiEndpointOffLineChargeTerm := by
  exact summable_xiEndpointCrossCharge.indicator xiEndpointOffLineSet

theorem xiEndpointOffLineChargeTerm_nonneg (q : XiZeroCopy) :
    0 ≤ xiEndpointOffLineChargeTerm q := by
  by_cases h : q ∈ xiEndpointOffLineSet
  · rw [xiEndpointOffLineChargeTerm, Set.indicator_of_mem h]
    simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q
  · rw [xiEndpointOffLineChargeTerm, Set.indicator_of_notMem h]

theorem xiEndpointOffLineChargeTerm_le_crossCharge (q : XiZeroCopy) :
    xiEndpointOffLineChargeTerm q ≤ xiEndpointCrossCharge q := by
  by_cases h : q ∈ xiEndpointOffLineSet
  · rw [xiEndpointOffLineChargeTerm, Set.indicator_of_mem h]
  · rw [xiEndpointOffLineChargeTerm, Set.indicator_of_notMem h]
    simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q

theorem xiEndpointOffLineCharge_nonneg : 0 ≤ xiEndpointOffLineCharge := by
  exact tsum_nonneg xiEndpointOffLineChargeTerm_nonneg

/-- The off-line charge is a positive part of the exact completed endpoint curvature. -/
theorem xiEndpointOffLineCharge_le_curvature :
    xiEndpointOffLineCharge ≤ xiEndpointCompletedCurvature := by
  have hle := summable_xiEndpointOffLineChargeTerm.tsum_le_tsum
    xiEndpointOffLineChargeTerm_le_crossCharge summable_xiEndpointCrossCharge
  change xiEndpointOffLineCharge ≤
    ∑' q : XiZeroCopy, xiEndpointCrossCharge q at hle
  rw [tsum_xiEndpointCrossCharge_eq_curvature] at hle
  exact hle

theorem xiEndpointOffLineCharge_lt_four : xiEndpointOffLineCharge < 4 :=
  xiEndpointOffLineCharge_le_curvature.trans_lt (by
    nlinarith [xiEndpointCompletedCurvature_lt_two_over_fortyThree])

/-- **Off-line self-budget quartet law.**  The four copies of an off-line zero are paid entirely
from the off-line endpoint charge, not from the full completed curvature. -/
theorem four_mul_xiEndpointCrossCharge_le_offLineCharge
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 * xiEndpointCrossCharge q ≤ xiEndpointOffLineCharge := by
  let qJ := xiZeroCopyLineConjEquiv q
  let qC := xiZeroCopyConjEquiv q
  let qCJ := xiZeroCopyLineConjEquiv qC
  let s : Finset XiZeroCopy := {q, qJ, qC, qCJ}
  have hqJ : q ≠ qJ := by
    simpa only [qJ] using xiZeroCopy_ne_lineConj_of_re_ne_half q hoff
  have hqC : q ≠ qC := by
    simpa only [qC] using xiZeroCopy_ne_conj q
  have hqCJ : q ≠ qCJ := by
    simpa only [qC, qCJ] using xiZeroCopy_ne_lineConjConj q
  have hqJqC : qJ ≠ qC := by
    simpa only [qJ, qC] using xiZeroCopy_lineConj_ne_conj q
  have hqJqCJ : qJ ≠ qCJ := by
    simpa only [qJ, qC, qCJ] using xiZeroCopy_lineConj_ne_lineConjConj q
  have hqCqCJ : qC ≠ qCJ := by
    simpa only [qC, qCJ] using
      xiZeroCopy_conj_ne_lineConjConj_of_re_ne_half q hoff
  have hoffJ : (qJ.1 : ℂ).re ≠ 1 / 2 := by
    simpa only [qJ] using xiEndpointOffLineSet_lineConj q hoff
  have hoffC : (qC.1 : ℂ).re ≠ 1 / 2 := by
    simpa only [qC] using xiEndpointOffLineSet_conj q hoff
  have hoffCJ : (qCJ.1 : ℂ).re ≠ 1 / 2 := by
    simpa only [qC, qCJ] using
      xiEndpointOffLineSet_lineConj (xiZeroCopyConjEquiv q)
        (xiEndpointOffLineSet_conj q hoff)
  have hle := summable_xiEndpointOffLineChargeTerm.sum_le_tsum s
    (fun j _ => xiEndpointOffLineChargeTerm_nonneg j)
  have hJ : xiEndpointCrossCharge qJ = xiEndpointCrossCharge q := by
    simpa only [qJ] using xiEndpointCrossCharge_lineConj q
  have hC : xiEndpointCrossCharge qC = xiEndpointCrossCharge q := by
    simpa only [qC] using xiEndpointCrossCharge_conj q
  have hCJ : xiEndpointCrossCharge qCJ = xiEndpointCrossCharge q := by
    calc
      xiEndpointCrossCharge qCJ = xiEndpointCrossCharge qC := by
        simpa only [qC, qCJ] using xiEndpointCrossCharge_lineConj qC
      _ = xiEndpointCrossCharge q := hC
  have hfinite : ∑ j ∈ s, xiEndpointOffLineChargeTerm j =
      4 * xiEndpointCrossCharge q := by
    simp only [s]
    rw [Finset.sum_insert (by simp [hqJ, hqC, hqCJ]),
      Finset.sum_insert (by simp [hqJqC, hqJqCJ]),
      Finset.sum_insert (by simp [hqCqCJ]), Finset.sum_singleton,
      xiEndpointOffLineChargeTerm_eq q hoff,
      xiEndpointOffLineChargeTerm_eq qJ hoffJ,
      xiEndpointOffLineChargeTerm_eq qC hoffC,
      xiEndpointOffLineChargeTerm_eq qCJ hoffCJ,
      hJ, hC, hCJ]
    ring
  rw [hfinite, ← xiEndpointOffLineCharge] at hle
  exact hle

/-- The self-budget quartet height law. -/
theorem four_le_offLineCharge_mul_one_add_im_sq
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 ≤ xiEndpointOffLineCharge * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) := by
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
  have horbit := four_mul_xiEndpointCrossCharge_le_offLineCharge q hoff
  have hden : 0 < (q.1 : ℂ).im ^ (2 : ℕ) + 1 := by positivity
  have hcharge : 4 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ≤
      4 * xiEndpointCrossCharge q := by
    calc
      4 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1) =
          4 * (1 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1)) := by ring
      _ ≤ 4 * xiEndpointCrossCharge q :=
        mul_le_mul_of_nonneg_left hlower (by norm_num)
  have hbudget : 4 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ≤
      xiEndpointOffLineCharge := hcharge.trans horbit
  rwa [div_le_iff₀ hden] at hbudget

/-- The off-line endpoint charge vanishes exactly on RH. -/
theorem xiEndpointOffLineCharge_eq_zero_iff_rh :
    xiEndpointOffLineCharge = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    apply xiThermalOrientationEnergy_eq_zero_iff_rh.mp
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      by_contra hoff
      have hwpos : 0 < xiEndpointCrossCharge q := by
        have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
        exact (by positivity : 0 < 1 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1)).trans_le hlower
      have htermpos : 0 < xiEndpointOffLineChargeTerm q := by
        rw [xiEndpointOffLineChargeTerm_eq q hoff]
        exact hwpos
      have hle := summable_xiEndpointOffLineChargeTerm.le_tsum q
        (fun j _ => xiEndpointOffLineChargeTerm_nonneg j)
      rw [← xiEndpointOffLineCharge, hzero] at hle
      linarith
    rw [xiThermalOrientationEnergy]
    have hfun : (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ)) =
        fun _ => 0 := by
      funext q
      rw [xiZeroCopyReciprocalSquare_im_formula, hline q]
      norm_num
    rw [hfun, tsum_zero]
  · intro hRH
    rw [xiEndpointOffLineCharge]
    have hfun : xiEndpointOffLineChargeTerm = fun _ => 0 := by
      funext q
      exact xiEndpointOffLineChargeTerm_eq_zero q
        (xi_divisor_support_re_eq_half_of_rh hRH q.1)
    rw [hfun, tsum_zero]

/-- The off-line endpoint charge is positive exactly when RH fails. -/
theorem xiEndpointOffLineCharge_pos_iff_not_rh :
    0 < xiEndpointOffLineCharge ↔ ¬RiemannHypothesis := by
  constructor
  · intro hpos hRH
    have hzero := xiEndpointOffLineCharge_eq_zero_iff_rh.mpr hRH
    linarith
  · intro hnot
    exact lt_of_le_of_ne xiEndpointOffLineCharge_nonneg (fun hzero =>
      hnot (xiEndpointOffLineCharge_eq_zero_iff_rh.mp hzero.symm))

/-- **Self-localized atomwise cubic law.**  The transverse energy of one copy is controlled by
the cube of its endpoint cross charge with a factor depending only on the total off-line charge. -/
theorem xiThermalOrientationTerm_le_offLineCharge_endpointCrossCharge_cube
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) ≤
      (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) *
        xiEndpointCrossCharge q ^ (3 : ℕ) := by
  have hB4 : xiEndpointOffLineCharge < 4 := xiEndpointOffLineCharge_lt_four
  have hden : 0 < 4 - xiEndpointOffLineCharge := sub_pos.mpr hB4
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hw : 0 ≤ xiEndpointCrossCharge q := by
      simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q
    rw [him, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (pow_nonneg (by positivity) 3) (pow_nonneg hw 3)
  · let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
    let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hu : u ≤ 1 / 4 := by
      have hstrip := xi_divisor_support_re_mem_open_unit q.1
      dsimp [u]
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv : 85 < v := by
      simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hon
    have hv0 : 0 < v := by linarith
    have huv0 : 0 < u + v := add_pos_of_nonneg_of_pos hu0 hv0
    have hcore : 4 * u * v ^ (4 : ℕ) ≤ (u + v) ^ (4 : ℕ) := by
      have hcoef : 4 * u ≤ 1 := by linarith
      have hleft : 4 * u * v ^ (4 : ℕ) ≤ v ^ (4 : ℕ) := by
        calc
          4 * u * v ^ (4 : ℕ) ≤ 1 * v ^ (4 : ℕ) :=
            mul_le_mul_of_nonneg_right hcoef (pow_nonneg hv0.le 4)
          _ = v ^ (4 : ℕ) := one_mul _
      have hright : v ^ (4 : ℕ) ≤ (u + v) ^ (4 : ℕ) := by
        exact pow_le_pow_left₀ hv0.le (by linarith) 4
      exact hleft.trans hright
    have heInv :
        (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) ≤ 1 / v ^ (3 : ℕ) := by
      rw [xiZeroCopyReciprocalSquare_im_formula]
      rw [show ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) = u by rfl,
        show (q.1 : ℂ).im ^ (2 : ℕ) = v by rfl, div_pow]
      rw [show (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) =
          4 * u * v by dsimp [u, v]; ring,
        show ((u + v) ^ (2 : ℕ)) ^ (2 : ℕ) = (u + v) ^ (4 : ℕ) by ring]
      rw [div_le_div_iff₀ (pow_pos huv0 4) (pow_pos hv0 3)]
      ring_nf at hcore ⊢
      exact hcore
    have hcross : 1 / (v + 1) ≤ xiEndpointCrossCharge q := by
      simpa only [v, xiEndpointCrossCharge] using
        endpoint_cross_term_re_ge_inv_one_add_im_sq q
    have hfour : 4 ≤ xiEndpointOffLineCharge * (v + 1) := by
      simpa only [v, add_comm] using
        four_le_offLineCharge_mul_one_add_im_sq q hon
    have hbase : 1 / v ≤
        (4 / (4 - xiEndpointOffLineCharge)) * (1 / (v + 1)) := by
      rw [show (4 / (4 - xiEndpointOffLineCharge)) * (1 / (v + 1)) =
          (4 / (4 - xiEndpointOffLineCharge)) / (v + 1) by ring]
      rw [div_le_div_iff₀ hv0 (by linarith : 0 < v + 1)]
      rw [show (4 / (4 - xiEndpointOffLineCharge)) * v =
          (4 * v) / (4 - xiEndpointOffLineCharge) by ring]
      rw [le_div_iff₀ hden]
      nlinarith
    have hInvCharge : 1 / v ≤
        (4 / (4 - xiEndpointOffLineCharge)) * xiEndpointCrossCharge q :=
      hbase.trans (mul_le_mul_of_nonneg_left hcross (by positivity))
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / v) hInvCharge 3
    calc
      (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) ≤ 1 / v ^ (3 : ℕ) := heInv
      _ = (1 / v) ^ (3 : ℕ) := by
        simpa only [one_div] using (inv_pow v 3).symm
      _ ≤ ((4 / (4 - xiEndpointOffLineCharge)) *
          xiEndpointCrossCharge q) ^ (3 : ℕ) := hpow
      _ = (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) *
          xiEndpointCrossCharge q ^ (3 : ℕ) := by rw [mul_pow]

/-- The four-copy cap converts the self-localized cubic law into a summable off-line charge
majorant. -/
theorem xiThermalOrientationTerm_le_offLineChargeCubicMajorant
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) ≤
      (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) *
        (xiEndpointOffLineCharge / 4) ^ (2 : ℕ) *
          xiEndpointOffLineChargeTerm q := by
  have hden0 : 0 ≤ 4 - xiEndpointOffLineCharge :=
    sub_nonneg.mpr xiEndpointOffLineCharge_lt_four.le
  have hfactor0 : 0 ≤ (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) :=
    pow_nonneg (div_nonneg (by norm_num) hden0) 3
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · rw [xiEndpointOffLineChargeTerm_eq_zero q hon]
    have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
  · have hw0 : 0 ≤ xiEndpointCrossCharge q := by
      simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg q
    have hwle : xiEndpointCrossCharge q ≤ xiEndpointOffLineCharge / 4 := by
      have hfour := four_mul_xiEndpointCrossCharge_le_offLineCharge q hon
      linarith
    have hwSq : xiEndpointCrossCharge q ^ (2 : ℕ) ≤
        (xiEndpointOffLineCharge / 4) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hw0 hwle 2
    have hwCube : xiEndpointCrossCharge q ^ (3 : ℕ) ≤
        (xiEndpointOffLineCharge / 4) ^ (2 : ℕ) * xiEndpointCrossCharge q := by
      calc
        xiEndpointCrossCharge q ^ (3 : ℕ) =
            xiEndpointCrossCharge q ^ (2 : ℕ) * xiEndpointCrossCharge q := by ring
        _ ≤ (xiEndpointOffLineCharge / 4) ^ (2 : ℕ) * xiEndpointCrossCharge q :=
          mul_le_mul_of_nonneg_right hwSq hw0
    rw [xiEndpointOffLineChargeTerm_eq q hon]
    apply (xiThermalOrientationTerm_le_offLineCharge_endpointCrossCharge_cube q).trans
    calc
      (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) * xiEndpointCrossCharge q ^ (3 : ℕ) ≤
          (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) *
            ((xiEndpointOffLineCharge / 4) ^ (2 : ℕ) * xiEndpointCrossCharge q) :=
        mul_le_mul_of_nonneg_left hwCube hfactor0
      _ = (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) *
          (xiEndpointOffLineCharge / 4) ^ (2 : ℕ) * xiEndpointCrossCharge q := by ring

/-- **Self-localized global cubic law.**  Only the endpoint charge actually carried by off-line
copies pays for the complete transverse thermal defect. -/
theorem xiThermalOrientationEnergy_le_offLineChargeCubicBudget :
    xiThermalOrientationEnergy ≤ xiThermalOffLineChargeCubicBudget := by
  let A : ℝ := (4 / (4 - xiEndpointOffLineCharge)) ^ (3 : ℕ) *
    (xiEndpointOffLineCharge / 4) ^ (2 : ℕ)
  have hscaled : Summable
      (fun q : XiZeroCopy => A * xiEndpointOffLineChargeTerm q) :=
    summable_xiEndpointOffLineChargeTerm.mul_left A
  have hle := summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q => by
      simpa only [A, mul_assoc] using
        xiThermalOrientationTerm_le_offLineChargeCubicMajorant q)
    hscaled
  rw [← xiThermalOrientationEnergy] at hle
  have hden : 4 - xiEndpointOffLineCharge ≠ 0 :=
    ne_of_gt (sub_pos.mpr xiEndpointOffLineCharge_lt_four)
  calc
    xiThermalOrientationEnergy ≤
        ∑' q : XiZeroCopy, A * xiEndpointOffLineChargeTerm q := hle
    _ = A * (∑' q : XiZeroCopy, xiEndpointOffLineChargeTerm q) := tsum_mul_left
    _ = A * xiEndpointOffLineCharge := by rw [xiEndpointOffLineCharge]
    _ = xiThermalOffLineChargeCubicBudget := by
      dsimp [A, xiThermalOffLineChargeCubicBudget]
      field_simp [hden]

/-- The self-localized budget improves the source-only cubic endpoint budget. -/
theorem xiThermalOffLineChargeCubicBudget_le_exactCubicEndpointBudget :
    xiThermalOffLineChargeCubicBudget ≤ xiThermalExactCubicEndpointBudget := by
  have hB4 : xiEndpointOffLineCharge < 4 := xiEndpointOffLineCharge_lt_four
  have hC4 : xiEndpointCompletedCurvature < 4 := by
    nlinarith [xiEndpointCompletedCurvature_lt_two_over_fortyThree]
  have hratio : xiEndpointOffLineCharge / (4 - xiEndpointOffLineCharge) ≤
      xiEndpointCompletedCurvature / (4 - xiEndpointCompletedCurvature) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hB4) (sub_pos.mpr hC4)]
    nlinarith [xiEndpointOffLineCharge_le_curvature]
  have hratio0 : 0 ≤
      xiEndpointOffLineCharge / (4 - xiEndpointOffLineCharge) :=
    div_nonneg xiEndpointOffLineCharge_nonneg (sub_nonneg.mpr hB4.le)
  unfold xiThermalOffLineChargeCubicBudget xiThermalExactCubicEndpointBudget
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hratio0 hratio 3) (by norm_num)

/-- The off-line charge, its self-cubic budget, and the transverse thermal energy have the same
zero locus. -/
theorem xiThermal_offLineCharge_budget_energy_zero_tfae :
    [xiEndpointOffLineCharge = 0,
      xiThermalOffLineChargeCubicBudget = 0,
      xiThermalOrientationEnergy = 0,
      RiemannHypothesis].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    simp [xiThermalOffLineChargeCubicBudget, h]
  tfae_have 2 → 1 := by
    intro hbudget
    by_contra hcharge
    have hpos : 0 < xiEndpointOffLineCharge :=
      lt_of_le_of_ne xiEndpointOffLineCharge_nonneg (Ne.symm hcharge)
    have hden : 0 < 4 - xiEndpointOffLineCharge :=
      sub_pos.mpr xiEndpointOffLineCharge_lt_four
    have hratio : 0 < xiEndpointOffLineCharge / (4 - xiEndpointOffLineCharge) :=
      div_pos hpos hden
    unfold xiThermalOffLineChargeCubicBudget at hbudget
    nlinarith [pow_pos hratio 3]
  tfae_have 1 ↔ 4 := xiEndpointOffLineCharge_eq_zero_iff_rh
  tfae_have 3 ↔ 4 := xiThermalOrientationEnergy_eq_zero_iff_rh
  tfae_finish

end

end RHTower
