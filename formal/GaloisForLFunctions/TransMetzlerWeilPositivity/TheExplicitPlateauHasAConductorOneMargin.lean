import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters

/-!
# The conductor-one margin of the explicit plateau

For `φ₀ = transMetzlerProfile = plateau (1/1000)` the completed Robin shape satisfies
`β(φ₀)/‖φ₀‖² + q₀ ≥ (19/20)(24/25) + (499/500)² = 477001/250000`. With `log(2π) < 1839/1000` and
`-log c + c q₀ ≥ q₀ - 1/1000` for `c ∈ (0, 1 + 1/1000]`, the conductor-one completed adjunction
energy exceeds `68/1000`, and every conductor `m ≥ 2` lies strictly above conductor one because the
dyadic Ramanujan gap `2 log 2 > 6/5` dominates the pole shift.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics

/-- Completed Robin margin of the explicit plateau:
`477001/250000 ≤ β(φ₀)/‖φ₀‖² + completeWeilPoleShift φ₀ 1`. -/
theorem transMetzlerProfile_completed_robin_margin :
    (477001 : ℝ) / 250000 ≤
      bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) +
        completeWeilPoleShift transMetzlerProfile 1 := by
  have hshape := plateau_completed_shape_ge (η := etaZero) (δ := 1 / 20)
    etaZero_pos (by norm_num [etaZero]) (by norm_num) (by norm_num)
  have hnum : (477001 : ℝ) / 250000 =
      (1 - (1 / 20 : ℝ)) * (1 - 2 * etaZero / (1 / 20)) + (1 - 2 * etaZero) ^ 2 := by
    norm_num [etaZero]
  rw [hnum, completeWeilPoleShift, one_mul]
  exact hshape

/-- The conductor-one completed adjunction energy of `φ₀` exceeds `68/1000` throughout
`c ∈ (0, 1 + 1/1000]`. -/
theorem completeWeilAdjunctionEnergy_transMetzlerProfile_one_gt
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 + 1 / 1000) :
    (68 : ℝ) / 1000 < completeWeilAdjunctionEnergy transMetzlerProfile c 1 := by
  have hshape' : (1908 : ℝ) / 1000 <
      bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) +
        completeWeilPoleShift transMetzlerProfile 1 :=
    (by norm_num : (1908 : ℝ) / 1000 < 477001 / 250000).trans_le
      transMetzlerProfile_completed_robin_margin
  have h2pi := log_two_pi_lt
  have hq0_le : completeWeilPoleShift transMetzlerProfile 1 ≤ 1 := by
    simpa only [one_mul] using completeWeilPoleShift_le contDiff_transMetzlerProfile.continuous
      (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos zero_le_one
  have hq0_nonneg : 0 ≤ completeWeilPoleShift transMetzlerProfile 1 :=
    completeWeilPoleShift_nonneg transMetzlerProfile zero_le_one
  have hself : completeWeilSelfFinitePart transMetzlerProfile c =
      -Real.log (2 * Real.pi) - Real.log c +
        bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) := by
    rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
      Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc0.ne']
    ring
  have hshift_eq : completeWeilPoleShift transMetzlerProfile c =
      c * completeWeilPoleShift transMetzlerProfile 1 := by
    unfold completeWeilPoleShift; ring
  have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  have hram1 := log_le_ramanujanAdjunctionEnergy_sub 1
  simp only [Nat.cast_one, Real.log_one] at hram1
  rw [completeWeilAdjunctionEnergy, if_pos rfl, hself, hshift_eq]
  have hc_shift : completeWeilPoleShift transMetzlerProfile 1 - 1 / 1000 ≤
      -Real.log c + c * completeWeilPoleShift transMetzlerProfile 1 := by
    rcases le_or_gt c 1 with hle | hgt
    · have hnonneg := mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hq0_le)
      nlinarith only [hlogc, hnonneg]
    · nlinarith only [hlogc, hgt, hc1, hq0_le, hq0_nonneg]
  linarith only [hshape', h2pi, hc_shift, hram1]

/-- Every conductor `m ≥ 2` has completed adjunction energy strictly above conductor one on `φ₀`
throughout `c ∈ (0, 1 + 1/1000]`. -/
theorem completeWeilAdjunctionEnergy_transMetzlerProfile_one_lt
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 + 1 / 1000) {m : ℕ} (hm : 2 ≤ m) :
    completeWeilAdjunctionEnergy transMetzlerProfile c 1 <
      completeWeilAdjunctionEnergy transMetzlerProfile c m := by
  have hlog2 : (693 : ℝ) / 1000 < Real.log 2 := by
    linarith only [Real.log_two_gt_d9]
  have hgap := (SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_sub_one_ge
    (by omega : 1 < m)).1
  have hshift_le : completeWeilPoleShift transMetzlerProfile c ≤ c :=
    completeWeilPoleShift_le contDiff_transMetzlerProfile.continuous
      (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos hc0.le
  rw [completeWeilAdjunctionEnergy, completeWeilAdjunctionEnergy, if_pos rfl,
    if_neg (by omega), add_zero]
  linarith only [hlog2, hgap, hshift_le, hc1]

#print axioms transMetzlerProfile_completed_robin_margin
#print axioms completeWeilAdjunctionEnergy_transMetzlerProfile_one_gt
#print axioms completeWeilAdjunctionEnergy_transMetzlerProfile_one_lt

end GaloisForLFunctions.TransMetzlerWeilPositivity
