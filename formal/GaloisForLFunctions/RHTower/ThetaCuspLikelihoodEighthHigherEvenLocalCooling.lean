import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthFockSector

/-!
# Local cooling of higher-even eighth Fock grades

A local response bound `1670r < 1` improves the cubic higher-even Bell scalar from the
global `1/3000` ceiling to `1/200000`. Consequently complete higher-even Fock loss costs
at most `13/2` dominant exponential units instead of `1300/3`.
-/

namespace RHTower
noncomputable section

theorem thetaCuspLikelihoodEighthHigherEvenSectorTail_lt_oneOverTwoHundredThousand_of_1670_mul_lt_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 1670 * r < 1) :
    thetaCuspLikelihoodEighthHigherEvenSectorTail r < (1 / 200000 : ℝ) := by
  rcases eq_or_lt_of_le hr0 with rfl | hrpos
  · unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
    have hzero : (fun m : ℕ =>
        (((2 * (m + 2) : ℕ) : ℝ) ^ 7) *
          (0 : ℝ) ^ (2 * (m + 2) - 1)) = (fun _ : ℕ => (0 : ℝ)) := by
      funext m
      rw [zero_pow (by omega), mul_zero]
    rw [hzero]
    norm_num
  have hr1 : r < 1 / 1670 := by nlinarith
  have hr399 : 399 * r < 1 := by nlinarith
  have hden : 0 < 1 - 144 * r ^ 2 := by
    have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
    nlinarith
  have hinv : (1 - 144 * r ^ 2)⁻¹ < (19000 / 18999 : ℝ) := by
    rw [inv_eq_one_div]
    apply (one_div_lt hden (by norm_num)).2
    have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
    nlinarith
  have hrCube := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 3 ≠ 0)
  have htail :=
    (summable_thetaCuspLikelihoodEighthHigherEvenSectorTail_and_le hr0 hr399).2
  calc
    thetaCuspLikelihoodEighthHigherEvenSectorTail r ≤
        20736 * r ^ 3 * (1 - 144 * r ^ 2)⁻¹ := htail
    _ < 20736 * r ^ 3 * (19000 / 18999 : ℝ) := by gcongr
    _ < 20736 * (1 / 1670 : ℝ) ^ 3 * (19000 / 18999 : ℝ) := by gcongr
    _ < (1 / 200000 : ℝ) := by norm_num

theorem thetaCuspLikelihoodEighthHigherEvenFockLoss_le_thirteenHalves_of_1670_response_lt_one
    {x : ℝ} (hx : 0 ≤ x)
    (hrLocal : 1670 * thetaCuspHigherLikelihoodSpectralResponse
      (thetaCuspLikelihoodCoordinate x) < 1) :
    thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (13 / 2 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr : 1670 * r < 1 := by simpa only [B, r] using hrLocal
  have htail := thetaCuspLikelihoodEighthHigherEvenSectorTail_lt_oneOverTwoHundredThousand_of_1670_mul_lt_one hr0 hr
  have htail0 : 0 ≤ thetaCuspLikelihoodEighthHigherEvenSectorTail r := by
    unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
    exact tsum_nonneg fun k => by positivity
  have hmass := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_le hA hBA
  have hmass0 : 0 ≤
      ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B := by
    apply tsum_nonneg
    intro k
    unfold thetaCuspLikelihoodAtomEighthMonomialMass
    apply MeasureTheory.integral_nonneg
    intro t
    positivity
  unfold thetaCuspLikelihoodEighthHigherEvenFockLoss
  dsimp only [A, B, r]
  calc
    thetaCuspLikelihoodEighthHigherEvenSectorTail r *
          (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) ≤
        (1 / 200000 : ℝ) *
          (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) :=
      mul_le_mul_of_nonneg_right htail.le hmass0
    _ ≤ (1 / 200000 : ℝ) *
        (1300000 * A ^ 8 * Real.exp (-(3 * A))) := by gcongr
    _ = (13 / 2 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by ring

/-- The same cubic tail ceiling survives under the weaker local response bound `1650r < 1`. -/
theorem thetaCuspLikelihoodEighthHigherEvenSectorTail_lt_oneOverTwoHundredThousand_of_1650_mul_lt_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr : 1650 * r < 1) :
    thetaCuspLikelihoodEighthHigherEvenSectorTail r < (1 / 200000 : ℝ) := by
  rcases eq_or_lt_of_le hr0 with rfl | hrpos
  · unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
    have hzero : (fun m : ℕ =>
        (((2 * (m + 2) : ℕ) : ℝ) ^ 7) *
          (0 : ℝ) ^ (2 * (m + 2) - 1)) = (fun _ : ℕ => (0 : ℝ)) := by
      funext m
      rw [zero_pow (by omega), mul_zero]
    rw [hzero]
    norm_num
  have hr1 : r < 1 / 1650 := by nlinarith
  have hr399 : 399 * r < 1 := by nlinarith
  have hden : 0 < 1 - 144 * r ^ 2 := by
    have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
    nlinarith
  have hinv : (1 - 144 * r ^ 2)⁻¹ < (18000 / 17999 : ℝ) := by
    rw [inv_eq_one_div]
    apply (one_div_lt hden (by norm_num)).2
    have hrSq := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 2 ≠ 0)
    nlinarith
  have hrCube := pow_lt_pow_left₀ hr1 hr0 (by norm_num : 3 ≠ 0)
  have htail :=
    (summable_thetaCuspLikelihoodEighthHigherEvenSectorTail_and_le hr0 hr399).2
  calc
    thetaCuspLikelihoodEighthHigherEvenSectorTail r ≤
        20736 * r ^ 3 * (1 - 144 * r ^ 2)⁻¹ := htail
    _ < 20736 * r ^ 3 * (18000 / 17999 : ℝ) := by gcongr
    _ < 20736 * (1 / 1650 : ℝ) ^ 3 * (18000 / 17999 : ℝ) := by gcongr
    _ < (1 / 200000 : ℝ) := by norm_num

/-- Under `1650r < 1`, complete higher-even order-eight loss still costs at most `13/2`. -/
theorem thetaCuspLikelihoodEighthHigherEvenFockLoss_le_thirteenHalves_of_1650_response_lt_one
    {x : ℝ} (hx : 0 ≤ x)
    (hrLocal : 1650 * thetaCuspHigherLikelihoodSpectralResponse
      (thetaCuspLikelihoodCoordinate x) < 1) :
    thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (13 / 2 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr : 1650 * r < 1 := by simpa only [B, r] using hrLocal
  have htail :=
    thetaCuspLikelihoodEighthHigherEvenSectorTail_lt_oneOverTwoHundredThousand_of_1650_mul_lt_one
      hr0 hr
  have htail0 : 0 ≤ thetaCuspLikelihoodEighthHigherEvenSectorTail r := by
    unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
    exact tsum_nonneg fun k => by positivity
  have hmass := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_le hA hBA
  have hmass0 : 0 ≤
      ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B := by
    apply tsum_nonneg
    intro k
    unfold thetaCuspLikelihoodAtomEighthMonomialMass
    apply MeasureTheory.integral_nonneg
    intro t
    positivity
  unfold thetaCuspLikelihoodEighthHigherEvenFockLoss
  dsimp only [A, B, r]
  calc
    thetaCuspLikelihoodEighthHigherEvenSectorTail r *
          (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) ≤
        (1 / 200000 : ℝ) *
          (∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B) :=
      mul_le_mul_of_nonneg_right htail.le hmass0
    _ ≤ (1 / 200000 : ℝ) *
        (1300000 * A ^ 8 * Real.exp (-(3 * A))) := by gcongr
    _ = (13 / 2 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by ring

end
end RHTower
