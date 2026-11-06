import GaloisForLFunctions.Core
import Mathlib.Data.NNReal.Basic

/-!
# Multiplicity shapes and Young branching are different

For independent letters, the size-three occupancy shape `(2,1)` has mass three times the
ordered repeated-letter mass. Young down-transition gives half of this mass to each size-two
shape. The resulting row discrepancy is half the repeated-letter mass; it vanishes exactly
when at most one letter has positive weight.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.SymmetricCharacters

variable {A : Type*} [Fintype A]

/-- Mass of ordered distinct colors, the first occurring twice. -/
def repeatedLetterMass (w : A → NNReal) : ℝ :=
  ∑ a, ∑ b, if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ)

/-- Total mass of the occupancy shape `(2,1)` among three independent letters. -/
def hookContentMass (w : A → NNReal) : ℝ :=
  ∑ a, ∑ b, ∑ c,
    if (a = b ∧ a ≠ c) ∨ (a = c ∧ a ≠ b) ∨ (b = c ∧ b ≠ a)
    then (w a : ℝ) * (w b : ℝ) * (w c : ℝ) else 0

theorem repeatedLetterMass_nonneg (w : A → NNReal) : 0 ≤ repeatedLetterMass w := by
  unfold repeatedLetterMass
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg _) (w b).coe_nonneg

/-- The three possible locations of the singleton color have equal mass. -/
theorem hookContentMass_eq (w : A → NNReal) :
    hookContentMass w = 3 * repeatedLetterMass w := by
  have hpoint (a b c : A) :
      (if (a = b ∧ a ≠ c) ∨ (a = c ∧ a ≠ b) ∨ (b = c ∧ b ≠ a)
        then (w a : ℝ) * (w b : ℝ) * (w c : ℝ) else 0) =
      (if a = b then (if a = c then 0 else (w a : ℝ) ^ 2 * (w c : ℝ)) else 0) +
      (if a = c then (if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ)) else 0) +
      (if b = c then (if b = a then 0 else (w b : ℝ) ^ 2 * (w a : ℝ)) else 0) := by
    by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c; simp
      · simp [hac, pow_two]
    · by_cases hac : a = c
      · subst c; simp [hab, Ne.symm hab]; ring
      · by_cases hbc : b = c
        · subst c; simp [hab, Ne.symm hab]; ring
        · simp [hab, hac, hbc]
  unfold hookContentMass
  simp only [hpoint, Finset.sum_add_distrib]
  have h₁ : (∑ a, ∑ b, ∑ c,
      if a = b then (if a = c then 0 else (w a : ℝ) ^ 2 * (w c : ℝ)) else 0) =
      repeatedLetterMass w := by
    unfold repeatedLetterMass
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp
  have h₂ : (∑ a, ∑ b, ∑ c,
      if a = c then (if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ)) else 0) =
      repeatedLetterMass w := by
    simp [repeatedLetterMass]
  have h₃ : (∑ a, ∑ b, ∑ c,
      if b = c then (if b = a then 0 else (w b : ℝ) ^ 2 * (w a : ℝ)) else 0) =
      repeatedLetterMass w := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.sum_comm]
    rfl
  rw [h₁, h₂, h₃]
  ring

/-- The occupancy collision term is the difference of the first three power sums. -/
theorem repeatedLetterMass_eq (w : A → NNReal) :
    repeatedLetterMass w =
      (∑ a, (w a : ℝ)) * (∑ a, (w a : ℝ) ^ 2) - ∑ a, (w a : ℝ) ^ 3 := by
  have hsplit (a b : A) :
      (if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ)) +
      (if a = b then (w a : ℝ) ^ 3 else 0) = (w a : ℝ) ^ 2 * (w b : ℝ) := by
    by_cases h : a = b
    · subst b; simp; ring
    · simp [h]
  have hsum : repeatedLetterMass w + (∑ a, (w a : ℝ) ^ 3) =
      (∑ a, (w a : ℝ) ^ 2) * (∑ b, (w b : ℝ)) := by
    calc
      repeatedLetterMass w + (∑ a, (w a : ℝ) ^ 3) =
          ∑ a, ∑ b, ((if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ)) +
            (if a = b then (w a : ℝ) ^ 3 else 0)) := by
        simp [Finset.sum_add_distrib, repeatedLetterMass]
      _ = ∑ a, ∑ b, (w a : ℝ) ^ 2 * (w b : ℝ) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsplit a b))
      _ = (∑ a, (w a : ℝ) ^ 2) * (∑ b, (w b : ℝ)) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [mul_comm] at hsum
  linarith

/-- Exact failure of the Young row down-transition for occupancy shapes. -/
theorem content_young_branching_defect (w : A → NNReal) :
    (∑ a, (w a : ℝ) ^ 3) + hookContentMass w / 2 -
      (∑ a, (w a : ℝ)) * (∑ a, (w a : ℝ) ^ 2) = repeatedLetterMass w / 2 := by
  rw [hookContentMass_eq, repeatedLetterMass_eq]
  ring

/-- Ordinary multiplicity shapes obey this Young branching equation only in the one-color
case. This is an exact classification, including alphabets with zero-weight letters. -/
theorem repeatedLetterMass_eq_zero_iff (w : A → NNReal) :
    repeatedLetterMass w = 0 ↔ ∀ a b, w a = 0 ∨ w b = 0 ∨ a = b := by
  have hn (a b : A) : 0 ≤ if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ) := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg _) (w b).coe_nonneg
  unfold repeatedLetterMass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hn a b))]
  simp only [Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro a
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hn a b)]
  simp only [Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro b
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, mul_eq_zero, NNReal.coe_eq_zero]

end GaloisForLFunctions.SymmetricCharacters
