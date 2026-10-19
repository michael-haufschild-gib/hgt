import GaloisForLFunctions.RHTower.Sieve.DistanceLocalChanges
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Local changes against Dirichlet twists

Apply the finite-prime modification and conjugation mechanisms of Lemmas 12.1
and 18.1 of *Ordinary two-point correlations of multiplicative functions*
(OpenAI, September 24, 2026). The local change budget is independent of cutoff,
frequency, and character modulus. Character multiplication and conjugation have
exact transport formulas in the existing pretentious squared distance.

Source: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf
-/

open Finset
namespace RHTower.Sieve
noncomputable section

/-- Finite local changes have the same cutoff-independent budget against every character twist. -/
theorem abs_mulDistSqPair_patch_dirichletTwist_sub_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (f b : ℕ → ℂ) (S P : Finset ℕ) (t : ℝ) :
    |mulDistSqPair (finiteValuePatch S f b) (fun n => χ n * charFn t n) P -
      mulDistSqPair f (fun n => χ n * charFn t n) P| ≤
        ∑ p ∈ S, ‖f p - b p‖ / (p : ℝ) := by
  refine (abs_mulDistSqPair_patch_sub_le f b _ P S).trans ?_
  calc
    _ ≤ ∑ p ∈ P.filter (· ∈ S), ‖f p - b p‖ / (p : ℝ) := by
      refine sum_le_sum fun p _ => ?_
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      rw [norm_mul, norm_charFn, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
    _ ≤ ∑ p ∈ S, ‖f p - b p‖ / (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg
        (fun p hp => (mem_filter.mp hp).2)
        (fun p _ _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

/-- A character multiplier moves to the reference factor with conjugation. -/
theorem mulDistSqPair_dirichletTwist {q r : ℕ}
    (ψ : DirichletCharacter ℂ q) (χ : DirichletCharacter ℂ r)
    (f : ℕ → ℂ) (t : ℝ) (P : Finset ℕ) :
    mulDistSqPair (fun n => f n * ψ n) (fun n => χ n * charFn t n) P =
      mulDistSqPair f (fun n => χ n * (starRingEnd ℂ) (ψ n) * charFn t n) P := by
  rw [mulDistSqPair_mul_left]
  congr 1
  funext n
  ring

/-- Archimedean frequency reverses under conjugation. -/
theorem mulDistSqPair_conj_charFn (f : ℕ → ℂ) (t : ℝ) (P : Finset ℕ) :
    mulDistSqPair (fun n => (starRingEnd ℂ) (f n)) (charFn t) P =
      mulDistSqPair f (charFn (-t)) P := by
  rw [mulDistSqPair_conj_left]
  congr 1
  funext n
  rw [conj_charFn, charFn]
  congr 3
  ring

/-- Conjugating the original factor conjugates the reference character and reverses frequency. -/
theorem mulDistSqPair_conj_dirichletTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ → ℂ) (t : ℝ) (P : Finset ℕ) :
    mulDistSqPair (fun n => (starRingEnd ℂ) (f n)) (fun n => χ n * charFn t n) P =
      mulDistSqPair f (fun n => (starRingEnd ℂ) (χ n) * charFn (-t) n) P := by
  rw [mulDistSqPair_conj_left]
  congr 1
  funext n
  rw [map_mul]
  congr 1
  rw [conj_charFn, charFn]
  congr 3
  ring

end
end RHTower.Sieve
