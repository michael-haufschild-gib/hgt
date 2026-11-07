import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateHorizonBeforeEightyOneSixteenths
import GaloisForLFunctions.WindowTowerOfSpecZ.PositiveTateDimensionsFormAClosedInitialInterval

/-!
# The first Tate dimension ends at ratio five

At dimension one the Tate weights are `α = 1/(2√2)`, `β = 1/√3`, `χ = 1/2` and, from ratio five on,
`δ = 2/√5`. The exact criterion on `(log(9/2), log 5]` holds: the late Schur pivots are
`7/8 − (1/3)/(1 − α) ≥ 23/72` and `83/168`, and `(χ − α²)² = 9/64` is below their product. Just past
`log 5` the ratio-five edge joins two reflected twelve-vertex graphs; the pivots are `7/8`, `83/168`,
`49/83`, `64/147`, `365/512`, and the last one `49/83 − 2/√5 − 512/1095` is negative.

Since positivity in a fixed dimension descends to shorter windows, dimension one is Tate-positive
exactly on the windows of length `A ≤ log 5`.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

private theorem alpha_one_sq : thirdStageAlpha 1 ^ 2 = 1 / 8 := by
  rw [thirdStageAlpha_sq]
  norm_num

private theorem beta_one_sq : thirdStageBeta 1 ^ 2 = 1 / 3 := by
  unfold thirdStageBeta
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.rpow_one]
  norm_num

private theorem chi_one : thirdStageChi 1 = 1 / 2 := by
  norm_num [thirdStageChi]

private theorem alpha_one_le : thirdStageAlpha 1 ≤ 2 / 5 := by
  have h0 := thirdStageAlpha_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
  nlinarith only [h0, alpha_one_sq]

/-- Half the ratio-five weight at dimension one, `2/√5`, exceeds `2/3`. -/
private theorem two_thirds_le_delta_one : 2 / 3 ≤ fourthStageDelta 1 := by
  have h5 : Real.sqrt 5 ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  unfold fourthStageDelta
  rw [Real.rpow_one, le_div_iff₀ (by positivity)]
  nlinarith only [h5]

/-- The left late pivot at dimension one: `7/8 − (1/3)/(1 − α) ≥ 23/72`. -/
private theorem lateLeft_one_ge :
    23 / 72 ≤ thirdStageLateLeft (thirdStageAlpha 1) (thirdStageBeta 1) := by
  have hα := alpha_one_le
  have hq : 1 / 3 / (1 - thirdStageAlpha 1) ≤ 5 / 9 := by
    rw [div_le_iff₀ (by linarith only [hα])]
    linarith only [hα]
  unfold thirdStageLateLeft
  rw [alpha_one_sq, beta_one_sq]
  linarith only [hq]

private theorem lateRight_one :
    thirdStageLateRight (thirdStageAlpha 1) (thirdStageBeta 1) = 83 / 168 := by
  unfold thirdStageLateRight
  rw [alpha_one_sq, beta_one_sq]
  norm_num

/-- Dimension one is Tate-positive on the second part of stage three, through ratio five. -/
theorem tateFunction_one_nonneg_afterNineHalves {A : ℝ}
    (hA9 : Real.log (9 / 2) < A) (hA5 : A ≤ Real.log 5) :
    ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H 1 := by
  apply (tateFunction_nonneg_iff_thirdStage_afterNineHalves hA9 hA5 zero_le_one).mpr
  have hL := lateLeft_one_ge
  refine ⟨by rw [chi_one]; norm_num, by linarith only [hL], ?_⟩
  rw [chi_one, alpha_one_sq, lateRight_one]
  nlinarith only [hL]

private theorem fourthStageW_one :
    fourthStageW (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) = 49 / 83 := by
  simp only [fourthStageW, fourthStageV, fourthStageD, alpha_one_sq, beta_one_sq, chi_one]
  norm_num

private theorem fourthStageQ_one :
    fourthStageQ (thirdStageAlpha 1) (thirdStageBeta 1) (thirdStageChi 1) = 365 / 512 := by
  simp only [fourthStageQ, fourthStageP, fourthStageW_one, alpha_one_sq, beta_one_sq]
  norm_num

/-- Just past ratio five, the final pivot of the dimension-one Tate form is negative. -/
theorem exists_tateFunction_one_neg_beforeEightyOneSixteenths {A : ℝ}
    (hA5 : Real.log 5 < A) (hA81 : A ≤ Real.log (81 / 16)) :
    ∃ H : ℝ → ℝ, IsWindowTest A H ∧ tateFunction A H 1 < 0 := by
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have h := (tateFunction_nonneg_iff_fourthStage_beforeEightyOneSixteenths hA5 hA81
    zero_le_one).mp hno
  have hlast := h.2.2.2.2.2
  rw [fourthStageW_one, fourthStageQ_one, beta_one_sq] at hlast
  linarith only [hlast, two_thirds_le_delta_one]

/-- **The dimension-one Tate horizon.** Every window test of length `A` has
`τ_H(1) = ⟨ρ_A(J₁)H, H⟩ ≥ 0` exactly when `A ≤ log 5`. -/
theorem tateFunction_one_nonneg_iff_le_log_five (A : ℝ) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H 1) ↔ A ≤ Real.log 5 := by
  constructor
  · intro hpos
    by_contra hA
    rw [not_le] at hA
    have h81 : Real.log 5 < Real.log (81 / 16) := Real.log_lt_log (by norm_num) (by norm_num)
    obtain ⟨H, hH, hneg⟩ := exists_tateFunction_one_neg_beforeEightyOneSixteenths
      (lt_min hA h81) (min_le_right A _)
    have hmono := hpos H (hH.mono (min_le_left A _))
    rw [tateFunction_of_aperture_le (min_le_left A _) hH] at hmono
    linarith only [hmono, hneg]
  · intro hA H hH
    have h95 : Real.log (9 / 2) < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
    have hfive := tateFunction_one_nonneg_afterNineHalves h95 le_rfl H (hH.mono hA)
    rwa [tateFunction_of_aperture_le hA hH] at hfive

end GaloisForLFunctions.WindowTowerOfSpecZ
