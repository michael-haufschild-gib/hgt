import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsTheChargesAPotentialAndADirichletForm
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFirstBlockMatricesOfRatioFourAndSevenHaveAMargin

/-!
# The neutral part of the first block matrices is Lorentzian

The block matrix is the product of the two charges of the packet plus its neutral part: density,
jets and contacts. On the first step packets of ratio four and seven the neutral part has the
signature of an intersection form on a surface, one square of one sign and all others of the
other:

* it is positive definite on each of the two hyperplanes where a charge of the packet vanishes,
  with the margin of the block matrix (`sum_neutralBlock_four_ge`, `sum_neutralBlock_seven_ge`,
  `sum_neutralBlock_four_fine_ge`), because there the block matrix is its neutral part
  (`sum_neutralBlock_eq_of_charge_zero`);
* it is negative on the first block (`neutralBlock_one_one_neg`, `neutralBlock_two_two_neg`):
  the density of a low block is below zero and its jet is positive.

So the neutral part has exactly one negative square there, and the product of the charges, a
hyperbolic plane, is what makes the block matrix positive.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- On a packet with a vanishing charge the form of the block matrix is the form of its neutral
part. -/
theorem sum_neutralBlock_eq_of_charge_zero {Q R J : ℕ} {σ : ℕ → ℝ}
    (hσ : ∑ j ∈ range J, σ j = 0 ∨ ∑ j ∈ range J, σ j * blockDegree (R + j) = 0) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  rw [sum_blockMatrix_eq_charges_add_neutral]
  rcases hσ with h | h
  · rw [h, mul_zero, zero_mul, zero_add]
  · rw [h, mul_zero, zero_add]

/-- The jet of a block with itself is not negative. -/
theorem blockJet_self_nonneg (a : ℕ) : 0 ≤ blockJet a a := by
  unfold blockJet
  have h1 := xLogXDiff_pos (n := a + a + 1) (by omega)
  rw [Nat.sub_self, xLogXDiff_zero]
  linarith

/-- **The neutral part is negative on the first block.** -/
theorem neutralBlock_one_one_neg (Q : ℕ) : neutralBlock Q 1 1 < 0 := by
  rw [neutralBlock, blockMatrix_self le_rfl]
  have hJ := blockJet_self_nonneg 1
  have hρ : blockDensity 1 < 0 := by
    have h21 : xLogX (1 + 1) = 2 * Real.log 2 := by
      unfold xLogX
      norm_num
    have h11 : xLogX 1 = 0 := by
      unfold xLogX
      simp
    have hγ := Real.one_half_lt_eulerMascheroniConstant
    have hπ : Real.log 3 < Real.log Real.pi :=
      Real.log_lt_log (by norm_num) Real.pi_gt_three
    have h3 := log_three_mem.1
    have h2 := Real.log_two_lt_d9
    unfold blockDensity
    rw [h21, h11, log_two_pi]
    linarith
  linarith

/-- The neutral part is negative on the block `(2, 3]`. -/
theorem neutralBlock_two_two_neg (Q : ℕ) : neutralBlock Q 2 2 < 0 := by
  rw [neutralBlock, blockMatrix_self (by norm_num)]
  have hJ := blockJet_self_nonneg 2
  have hρ : blockDensity 2 < 0 := by
    have h32 : xLogX (2 + 1) = 3 * Real.log 3 := by
      unfold xLogX
      norm_num
    have h22 : xLogX 2 = 2 * Real.log 2 := by
      unfold xLogX
      norm_num
    have hγ := Real.one_half_lt_eulerMascheroniConstant
    have hπ : Real.log 3 < Real.log Real.pi :=
      Real.log_lt_log (by norm_num) Real.pi_gt_three
    have h3 := log_three_mem.2
    have h2 := Real.log_two_gt_d9
    unfold blockDensity
    rw [h32, h22, log_two_pi]
    linarith
  linarith

/-- **The neutral part of ratio four on the unit blocks of `(1, 4]` is positive where a charge
vanishes.** -/
theorem sum_neutralBlock_four_ge {σ : ℕ → ℝ}
    (hσ : ∑ j ∈ range 3, σ j = 0 ∨ ∑ j ∈ range 3, σ j * blockDegree (1 + j) = 0) :
    1 / 20 * ∑ j ∈ range 3, σ j ^ 2 ≤
      ∑ j ∈ range 3, ∑ l ∈ range 3, σ j * σ l * neutralBlock 4 (1 + j) (1 + l) := by
  rw [sum_neutralBlock_eq_of_charge_zero hσ]
  exact sum_blockMatrix_four_ge σ

/-- **The neutral part of ratio seven on the unit blocks of `(1, 7]` is positive where a charge
vanishes.** -/
theorem sum_neutralBlock_seven_ge {σ : ℕ → ℝ}
    (hσ : ∑ j ∈ range 6, σ j = 0 ∨ ∑ j ∈ range 6, σ j * blockDegree (1 + j) = 0) :
    1 / 100 * ∑ j ∈ range 6, σ j ^ 2 ≤
      ∑ j ∈ range 6, ∑ l ∈ range 6, σ j * σ l * neutralBlock 7 (1 + j) (1 + l) := by
  rw [sum_neutralBlock_eq_of_charge_zero hσ]
  exact sum_blockMatrix_seven_ge σ

/-- **The neutral part of ratio four on the unit blocks of `(2, 8]` is positive where a charge
vanishes.** -/
theorem sum_neutralBlock_four_fine_ge {σ : ℕ → ℝ}
    (hσ : ∑ j ∈ range 6, σ j = 0 ∨ ∑ j ∈ range 6, σ j * blockDegree (2 + j) = 0) :
    1 / 100 * ∑ j ∈ range 6, σ j ^ 2 ≤
      ∑ j ∈ range 6, ∑ l ∈ range 6, σ j * σ l * neutralBlock 4 (2 + j) (2 + l) := by
  rw [sum_neutralBlock_eq_of_charge_zero hσ]
  exact sum_blockMatrix_four_fine_ge σ

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
