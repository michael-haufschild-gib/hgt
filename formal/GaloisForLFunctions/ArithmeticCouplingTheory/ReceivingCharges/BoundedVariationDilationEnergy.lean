import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonLawsHoldForProfilesOfBoundedVariation

/-!
# Dilation energy of neutral profiles with bounded variation

The prime form of a neutral step profile has only harmonic-size growth.
The Mertens diagonal therefore supplies its leading dilation energy:
the horizon logarithm times its harmonic square mass.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory

/-- Horizon variation is subadditive. -/
theorem horizonVariation_add_le (F G : ℕ → ℝ) (N : ℕ) :
    horizonVariation (fun n => F n + G n) N ≤ horizonVariation F N + horizonVariation G N := by
  rw [horizonVariation, horizonVariation, horizonVariation, ← sum_add_distrib]
  apply sum_le_sum
  intro n _
  have he : horizonDiff (fun n => F n + G n) N n =
      horizonDiff F N n + horizonDiff G N n := by
    unfold horizonDiff
    split_ifs <;> ring
  rw [he]
  exact abs_add_le _ _

/-- Multiplying a profile scales its horizon variation by the absolute scalar. -/
theorem horizonVariation_const_mul (F : ℕ → ℝ) (N : ℕ) (s : ℝ) :
    horizonVariation (fun n => s * F n) N = |s| * horizonVariation F N := by
  rw [horizonVariation, horizonVariation, mul_sum]
  apply sum_congr rfl
  intro n _
  have he : horizonDiff (fun n => s * F n) N n = s * horizonDiff F N n := by
    unfold horizonDiff
    split_ifs <;> ring
  rw [he, abs_mul]

/-- Subtracting profiles costs the sum of their variations. -/
theorem horizonVariation_sub_le (F G : ℕ → ℝ) (N : ℕ) :
    horizonVariation (fun n => F n - G n) N ≤ horizonVariation F N + horizonVariation G N := by
  have h := horizonVariation_add_le F (fun n => (-1 : ℝ) * G n) N
  rw [horizonVariation_const_mul] at h
  simpa only [neg_one_mul, ← sub_eq_add_neg, abs_neg, abs_one, one_mul] using h

/-- A prefix indicator has at most one jump, including its terminal jump. -/
theorem horizonVariation_prefix_le (M N : ℕ) :
    horizonVariation (fun n => if n ≤ M then (1 : ℝ) else 0) N ≤ 1 := by
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      |horizonDiff (fun n => if n ≤ M then (1 : ℝ) else 0) N n| =
        if n = min M N then 1 else 0 := by
    have hnN := (mem_Icc.mp hn).2
    by_cases hnM : n ≤ M
    · by_cases hlt : n < N
      · by_cases hnext : n + 1 ≤ M
        · have hne : n ≠ min M N := by omega
          simp only [horizonDiff, if_pos hnM, if_pos hlt, if_pos hnext, if_neg hne,
            sub_self, abs_zero]
        · have he : n = min M N := by omega
          simp only [horizonDiff, if_pos hnM, if_pos hlt, if_neg hnext, if_pos he,
            sub_zero, abs_one]
      · have he : n = min M N := by omega
        simp only [horizonDiff, if_pos hnM, if_neg hlt, if_pos he, sub_zero, abs_one]
    · have hnext : ¬n + 1 ≤ M := by omega
      have hne : n ≠ min M N := by omega
      simp only [horizonDiff, if_neg hnM, if_neg hnext, ite_self, sub_zero,
        abs_zero, if_neg hne]
  rw [horizonVariation, sum_congr rfl hpoint, sum_ite_eq']
  split_ifs <;> norm_num

/-- Neutrality removes the rank-one horizon divergence from the prime form. -/
theorem abs_primeDilationForm_le_variation (N : ℕ) (F : ℕ → ℝ)
    (hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) :
    |primeDilationForm N F| ≤
      (Real.log 8 + 5) * RenormalizedArithmeticPotentialTheory.harmonicSum N *
        horizonVariation F N ^ 2 := by
  have hp : polarFunctional N (fun n => F n * poleVector n) = 0 := by
    calc
      _ = ∑ n ∈ Icc 1 N, F n / (n : ℝ) := by
        apply sum_congr rfl
        intro n _
        rw [mul_assoc, ← sq, poleVector_sq]
        ring
      _ = 0 := hF
  have he : (fun n => F n * poleVector n) = atomAmplitude F := by
    funext n
    simp only [atomAmplitude, poleVector, mul_one_div]
  have h := abs_atomicWeilForm_profile_sub_le F N
  rw [hp, sq, mul_zero, sub_zero, he, atomicWeilForm_atomAmplitude] at h
  exact h

/-- The Mertens diagonal differs from the horizon logarithm by a bounded row. -/
theorem abs_mertensDiagonal_sub_log_mass_le (N : ℕ) (F : ℕ → ℝ) :
    |mertensDiagonal N F - Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))| ≤
      (Real.log 8 + 4) * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) := by
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      |mertensSum (N / n) + Real.log n - Real.log N| ≤ Real.log 8 + 4 := by
    have hlo := row_ge (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
    have hhi := row_le (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
    change Real.log N - (Real.log 8 + 4) ≤ mertensSum (N / n) + Real.log n at hlo
    change mertensSum (N / n) + Real.log n ≤ Real.log N + (Real.log 4 + 4) at hhi
    have h48 : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    rw [abs_le]
    constructor <;> linarith only [hlo, hhi, h48]
  have he : mertensDiagonal N F - Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) =
      ∑ n ∈ Icc 1 N,
        (mertensSum (N / n) + Real.log n - Real.log N) * (F n ^ 2 / (n : ℝ)) := by
    rw [mertensDiagonal, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [he, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ F n ^ 2 / (n : ℝ))]
  exact mul_le_mul_of_nonneg_right (hrow n hn) (by positivity)

/-- Bounded variation gives the exact leading neutral dilation energy. -/
theorem abs_jumpEnergy_sub_log_mass_le_variation (N : ℕ) (F : ℕ → ℝ)
    (hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) :
    |jumpEnergy N F - Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))| ≤
      (Real.log 8 + 4) * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
        (Real.log 8 + 5) * RenormalizedArithmeticPotentialTheory.harmonicSum N *
          horizonVariation F N ^ 2 := by
  have he : jumpEnergy N F - Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) =
      (mertensDiagonal N F - Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))) -
        primeDilationForm N F := by rw [primeDilationForm_eq]; ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add (abs_mertensDiagonal_sub_log_mass_le N F)
    (abs_primeDilationForm_le_variation N F hF))

#print axioms abs_jumpEnergy_sub_log_mass_le_variation

end GaloisForLFunctions.ArithmeticCouplingTheory
