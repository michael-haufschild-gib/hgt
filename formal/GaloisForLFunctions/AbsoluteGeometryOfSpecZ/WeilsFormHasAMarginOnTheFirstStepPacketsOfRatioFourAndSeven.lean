import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheMatrixOfAStepPacketIsTheMixedDifferenceOfItsWindows
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFirstBlockMatricesOfRatioFourAndSevenHaveAMargin
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheStepPacketMatricesAtFiniteScaleHaveAnExplicitError

/-!
# Weil's form has a margin on the first step packets of ratio four and seven

The windows `(1, 4]` and `(1, 7]` are the first with the contacts of two and of three primes.
Their lengths `log 4` and `log 7` are beyond the lengths on which the sign of Weil's form is
proved for all packets.

* **Ratio four** (`packetForm_stepPacket_ratioFour_ge`). On the step packets of the three blocks
  `(1, 2], (2, 3], (3, 4]`, `𝔚_4 ≥ (1/20) Σ σ_j²`. The contacts are those of `2` and `3`.
* **Ratio seven** (`packetForm_stepPacket_ratioSeven_ge`). On the step packets of the six blocks
  of `(1, 7]`, `𝔚_7 ≥ (1/100) Σ σ_j²`. The contacts are those of `2`, `3`, `4`, `5`.
* **Ratio four on finer blocks** (`packetForm_stepPacket_ratioFour_fine_ge`). On the step
  packets of the six unit blocks of `(2, 8]`, the same window on blocks of half the size,
  `𝔚_4 ≥ (1/100) Σ σ_j²`; on the comb, for `B ≥ 3000000`, a divisor constant on the six blocks
  of `B` points of `(2B, 8B]` has form at least `(1/200) B Σ σ_j²`
  (`combForm_ratioFour_fine_ge`).
* **The comb at explicit block sizes** (`combForm_ratioFour_ge`, `combForm_ratioSeven_ge`). For
  `B ≥ 300000` every real divisor constant on the three blocks of `B` points of `(B, 4B]` has
  Weil's form on the comb at least `(1/40) B Σ σ_j²`; for `B ≥ 3000000` every real divisor
  constant on the six blocks of `(B, 7B]` has it at least `(1/200) B Σ σ_j²`.

The matrices are those of the degrees, the jets and the floor maps; the margins are certified in
the module on the first block matrices. The transfer to the comb is the explicit block error.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (blockIndex)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

/-! ### The sign of the matrices -/

/-- **Ratio four.** Weil's form `𝔚_4` on the step packets of the blocks `(1, 2], (2, 3], (3, 4]`
is at least `(1/20) Σ σ_j²`. -/
theorem packetForm_stepPacket_ratioFour_ge (σ : ℕ → ℝ) :
    1 / 20 * ∑ j ∈ range 3, σ j ^ 2 ≤ packetForm 4 (stepPacket 1 3 σ) := by
  rw [packetForm_stepPacket_eq_sum_blockMatrix le_rfl]
  exact sum_blockMatrix_four_ge σ

/-- **Ratio seven.** Weil's form `𝔚_7` on the step packets of the six blocks of `(1, 7]` is at
least `(1/100) Σ σ_j²`. -/
theorem packetForm_stepPacket_ratioSeven_ge (σ : ℕ → ℝ) :
    1 / 100 * ∑ j ∈ range 6, σ j ^ 2 ≤ packetForm 7 (stepPacket 1 6 σ) := by
  rw [packetForm_stepPacket_eq_sum_blockMatrix le_rfl]
  exact sum_blockMatrix_seven_ge σ

/-- **Ratio four on finer blocks.** Weil's form `𝔚_4` on the step packets of the six unit
blocks of `(2, 8]` is at least `(1/100) Σ σ_j²`. -/
theorem packetForm_stepPacket_ratioFour_fine_ge (σ : ℕ → ℝ) :
    1 / 100 * ∑ j ∈ range 6, σ j ^ 2 ≤ packetForm 4 (stepPacket 2 6 σ) := by
  rw [packetForm_stepPacket_eq_sum_blockMatrix (by norm_num)]
  exact sum_blockMatrix_four_fine_ge σ

/-! ### The block error at explicit sizes -/

/-- The tangent of the logarithm at `M`. -/
theorem log_le_div_add {x M : ℝ} (hx : 0 < x) (hM : 0 < M) :
    Real.log x ≤ x / M + Real.log M - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hM)
  rw [Real.log_div hx.ne' hM.ne'] at h
  linarith

/-- The block error of ratio four is below half the margin from `B = 300000` on. -/
theorem windowError_ratioFour_le {B : ℕ} (hB : 300000 ≤ B) :
    6 * (((3 : ℕ) : ℝ) + 1) * windowError (1 + 3) 4 B ≤ 1 / 20 / 2 := by
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hB1 : (300000 : ℝ) ≤ B := by exact_mod_cast hB
  have hM : Real.log (8000000 : ℝ) = 9 * Real.log 2 + 6 * Real.log 5 := by
    rw [show (8000000 : ℝ) = 2 ^ 9 * 5 ^ 6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hc : ((2 * (1 + 3) * B : ℕ) : ℝ) / 8000000 = (B : ℝ) / 1000000 := by
    push_cast
    ring
  have hlog := log_le_div_add (x := ((2 * (1 + 3) * B : ℕ) : ℝ)) (M := 8000000)
    (Nat.cast_pos.mpr (by omega)) (by norm_num)
  rw [hM, hc] at hlog
  rw [windowError, sum_vonMangoldt_Icc_two_four, log_twelve, mul_div_assoc', div_le_iff₀ hB0]
  push_cast at hlog ⊢
  linarith [Real.log_two_lt_d9, log_three_mem.2, log_five_mem.2]

/-- The block error of ratio four on six blocks is below half the margin from `B = 3000000`
on. -/
theorem windowError_ratioFour_fine_le {B : ℕ} (hB : 3000000 ≤ B) :
    6 * (((6 : ℕ) : ℝ) + 1) * windowError (2 + 6) 4 B ≤ 1 / 100 / 2 := by
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hB1 : (3000000 : ℝ) ≤ B := by exact_mod_cast hB
  have hM : Real.log (64000000 : ℝ) = 12 * Real.log 2 + 6 * Real.log 5 := by
    rw [show (64000000 : ℝ) = 2 ^ 12 * 5 ^ 6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hc : ((2 * (2 + 6) * B : ℕ) : ℝ) / 64000000 = (B : ℝ) / 4000000 := by
    push_cast
    ring
  have hlog := log_le_div_add (x := ((2 * (2 + 6) * B : ℕ) : ℝ)) (M := 64000000)
    (Nat.cast_pos.mpr (by omega)) (by norm_num)
  rw [hM, hc] at hlog
  rw [windowError, sum_vonMangoldt_Icc_two_four, log_twelve, mul_div_assoc', div_le_iff₀ hB0]
  push_cast at hlog ⊢
  linarith [Real.log_two_lt_d9, log_three_mem.2, log_five_mem.2]

theorem log_fourHundredTwenty :
    Real.log 420 = 2 * Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (420 : ℝ) = 2 ^ 2 * 3 * 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast
  ring

/-- The block error of ratio seven is below half the margin from `B = 3000000` on. -/
theorem windowError_ratioSeven_le {B : ℕ} (hB : 3000000 ≤ B) :
    6 * (((6 : ℕ) : ℝ) + 1) * windowError (1 + 6) 7 B ≤ 1 / 100 / 2 := by
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hB1 : (3000000 : ℝ) ≤ B := by exact_mod_cast hB
  have hM : Real.log (56000000 : ℝ) = 9 * Real.log 2 + 6 * Real.log 5 + Real.log 7 := by
    rw [show (56000000 : ℝ) = 2 ^ 9 * 5 ^ 6 * 7 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hc : ((2 * (1 + 6) * B : ℕ) : ℝ) / 56000000 = (B : ℝ) / 4000000 := by
    push_cast
    ring
  have hlog := log_le_div_add (x := ((2 * (1 + 6) * B : ℕ) : ℝ)) (M := 56000000)
    (Nat.cast_pos.mpr (by omega)) (by norm_num)
  rw [hM, hc] at hlog
  rw [windowError, sum_vonMangoldt_Icc_two_seven, log_fourHundredTwenty, mul_div_assoc',
    div_le_iff₀ hB0]
  push_cast at hlog ⊢
  linarith [Real.log_two_lt_d9, log_three_mem.2, log_five_mem.2, log_seven_mem.2]

/-! ### The comb -/

/-- **The comb of ratio four at explicit block sizes.** For `B ≥ 300000`, Weil's form on the
comb of a real divisor constant on the three blocks of `B` points of `(B, 4B]` is at least
`(1/40) B Σ σ_j²`. -/
theorem combForm_ratioFour_ge {B : ℕ} (hB : 300000 ≤ B) (σ : ℕ → ℝ) :
    1 / 40 * B * ∑ j ∈ range 3, σ j ^ 2 ≤
      combW (Ioc B (B + B * 3)) (fun n => σ (blockIndex B B n)) := by
  have h := le_combForm_of_packetForm_ge (R := 1) (J := 3) (Q := 4) (B := B) le_rfl
    (by norm_num) (by omega) packetForm_stepPacket_ratioFour_ge (windowError_ratioFour_le hB) σ
  simp only [one_mul] at h
  rw [show (1 : ℝ) / 20 / 2 = 1 / 40 by norm_num] at h
  exact h

/-- **The comb of ratio seven at explicit block sizes.** For `B ≥ 3000000`, Weil's form on the
comb of a real divisor constant on the six blocks of `B` points of `(B, 7B]` is at least
`(1/200) B Σ σ_j²`. -/
theorem combForm_ratioSeven_ge {B : ℕ} (hB : 3000000 ≤ B) (σ : ℕ → ℝ) :
    1 / 200 * B * ∑ j ∈ range 6, σ j ^ 2 ≤
      combW (Ioc B (B + B * 6)) (fun n => σ (blockIndex B B n)) := by
  have h := le_combForm_of_packetForm_ge (R := 1) (J := 6) (Q := 7) (B := B) le_rfl
    (by norm_num) (by omega) packetForm_stepPacket_ratioSeven_ge (windowError_ratioSeven_le hB) σ
  simp only [one_mul] at h
  rw [show (1 : ℝ) / 100 / 2 = 1 / 200 by norm_num] at h
  exact h

/-- **The comb of ratio four on finer blocks.** For `B ≥ 3000000`, Weil's form on the comb of a
real divisor constant on the six blocks of `B` points of `(2B, 8B]` is at least
`(1/200) B Σ σ_j²`. -/
theorem combForm_ratioFour_fine_ge {B : ℕ} (hB : 3000000 ≤ B) (σ : ℕ → ℝ) :
    1 / 200 * B * ∑ j ∈ range 6, σ j ^ 2 ≤
      combW (Ioc (2 * B) (2 * B + B * 6)) (fun n => σ (blockIndex (2 * B) B n)) := by
  have h := le_combForm_of_packetForm_ge (R := 2) (J := 6) (Q := 4) (B := B) (by norm_num)
    (by norm_num) (by omega) packetForm_stepPacket_ratioFour_fine_ge
    (windowError_ratioFour_fine_le hB) σ
  rw [show (1 : ℝ) / 100 / 2 = 1 / 200 by norm_num] at h
  exact h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
