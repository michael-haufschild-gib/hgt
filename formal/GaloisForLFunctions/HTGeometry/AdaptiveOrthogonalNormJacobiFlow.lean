import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy

/-!
# Norm flow of a finite monic orthogonal admission

The shifted moment transport differentiates the norm through the Euler polynomial
`X E₁(Pₙ²)`.  This file computes its only surviving orthogonal projection.  The result is the
exact norm-flow coefficient `2 aₙ - (2n+1) αₙ`, where `aₙ` is the first subleading coefficient of
`Pₙ`.  All arguments use one finite positive Hankel block.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

noncomputable section

/-- Derivative companion appearing in the norm transport. -/
def adaptiveOrthoNormCompanion (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  X ^ (2 : ℕ) * (monicOrtho s n).derivative

/-- Remainder after removing the only two orthogonal degrees visible to `Pₙ`. -/
def adaptiveOrthoNormRemainder (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  adaptiveOrthoNormCompanion s n -
      (n : ℝ) • monicOrtho s (n + 1) -
    ((n : ℝ) * monicOrthoAlpha s n - monicOrthoFirstCoeff s n) •
      monicOrtho s n

theorem adaptiveOrthoNormCompanion_coeff_add_one (s : ℕ → ℝ) (n : ℕ) :
    (adaptiveOrthoNormCompanion s n).coeff (n + 1) = (n : ℝ) := by
  rcases n with _ | n
  · simp [adaptiveOrthoNormCompanion]
  · simp [adaptiveOrthoNormCompanion, Polynomial.coeff_X_pow_mul',
      Polynomial.coeff_derivative]

theorem adaptiveOrthoNormCompanion_coeff_self
    (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoNormCompanion s n).coeff n =
      ((n - 1 : ℕ) : ℝ) * monicOrthoFirstCoeff s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rcases k with _ | k
  · simp [adaptiveOrthoNormCompanion, Polynomial.coeff_X_pow_mul',
      monicOrthoFirstCoeff]
  · simp [adaptiveOrthoNormCompanion, Polynomial.coeff_X_pow_mul',
      Polynomial.coeff_derivative, monicOrthoFirstCoeff]
    ring

theorem adaptiveOrthoNormCompanion_coeff_eq_zero_of_add_one_lt
    (s : ℕ → ℝ) {n k : ℕ} (hnk : n + 1 < k) :
    (adaptiveOrthoNormCompanion s n).coeff k = 0 := by
  have h2 : 2 ≤ k := by omega
  have hnsub : n < k - 1 := by omega
  have hp : (monicOrtho s n).coeff (k - 1) = 0 :=
    coeff_monicOrtho_eq_zero_of_lt s hnsub
  rw [adaptiveOrthoNormCompanion, Polynomial.coeff_X_pow_mul', if_pos h2,
    Polynomial.coeff_derivative]
  rw [show k - 2 + 1 = k - 1 by omega, hp]
  ring

theorem adaptiveOrthoNormRemainder_coeff_add_one (s : ℕ → ℝ) (n : ℕ) :
    (adaptiveOrthoNormRemainder s n).coeff (n + 1) = 0 := by
  have h0 : (monicOrtho s n).coeff (n + 1) = 0 :=
    coeff_monicOrtho_eq_zero_of_lt s (by omega)
  simp [adaptiveOrthoNormRemainder, adaptiveOrthoNormCompanion_coeff_add_one,
    h0]

theorem adaptiveOrthoNormRemainder_coeff_self
    {s : ℕ → ℝ} (h : PositiveMomentFormBelow s N) {n : ℕ}
    (hn : 0 < n) (hnN : n + 1 ≤ N) :
    (adaptiveOrthoNormRemainder s n).coeff n = 0 := by
  rw [adaptiveOrthoNormRemainder, Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_smul, Polynomial.coeff_smul,
    adaptiveOrthoNormCompanion_coeff_self s hn]
  have hnext : (monicOrtho s (n + 1)).coeff n =
      monicOrthoFirstCoeff s (n + 1) := by rfl
  rw [hnext, coeff_monicOrtho_self,
    monicOrthoFirstCoeff_succ_below h hnN]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  ring

theorem degree_adaptiveOrthoNormRemainder_lt
    {s : ℕ → ℝ} (h : PositiveMomentFormBelow s N) {n : ℕ}
    (hn : 0 < n) (hnN : n + 1 ≤ N) :
    (adaptiveOrthoNormRemainder s n).degree < (n : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hnk
  by_cases hhigh : n + 1 < k
  · have hn1 : (monicOrtho s (n + 1)).coeff k = 0 :=
      coeff_monicOrtho_eq_zero_of_lt s hhigh
    have hn0 : (monicOrtho s n).coeff k = 0 :=
      coeff_monicOrtho_eq_zero_of_lt s (by omega)
    simp [adaptiveOrthoNormRemainder,
      adaptiveOrthoNormCompanion_coeff_eq_zero_of_add_one_lt s hhigh, hn1, hn0]
  · rcases (by omega : k = n ∨ k = n + 1) with rfl | rfl
    · exact adaptiveOrthoNormRemainder_coeff_self h hn hnN
    · exact adaptiveOrthoNormRemainder_coeff_add_one s n

/-- Exact orthogonal projection of `X²Pₙ'`. -/
theorem momentInner_monicOrtho_adaptiveOrthoNormCompanion
    {s : ℕ → ℝ} (h : PositiveMomentFormBelow s N) {n : ℕ}
    (hn : 0 < n) (hnN : n + 1 ≤ N) :
    momentInner s (monicOrtho s n) (adaptiveOrthoNormCompanion s n) =
      ((n : ℝ) * monicOrthoAlpha s n - monicOrthoFirstCoeff s n) *
        monicOrthoNormSq s n := by
  have hhigh : momentInner s (monicOrtho s n) (monicOrtho s (n + 1)) = 0 :=
    monicOrtho_inner_eq_zero_below h (by omega) hnN (by omega)
  have hrem : momentInner s (monicOrtho s n)
      (adaptiveOrthoNormRemainder s n) = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt_below h (by omega)
      (degree_adaptiveOrthoNormRemainder_lt h hn hnN)
  rw [show adaptiveOrthoNormCompanion s n =
      (n : ℝ) • monicOrtho s (n + 1) +
        ((n : ℝ) * monicOrthoAlpha s n - monicOrthoFirstCoeff s n) •
          monicOrtho s n + adaptiveOrthoNormRemainder s n by
      unfold adaptiveOrthoNormRemainder
      module]
  rw [momentInner_add_right, momentInner_add_right,
    momentInner_smul_right, momentInner_smul_right, hhigh, hrem]
  simp [monicOrthoNormSq]

/-- Euler transport of `Pₙ²` collapses to the norm-flow coefficient. -/
theorem momentFunctional_X_shiftedEuler_one_sq_monicOrtho
    {s : ℕ → ℝ} (h : PositiveMomentFormBelow s N) {n : ℕ}
    (hn : 0 < n) (hnN : n + 1 ≤ N) :
    momentFunctional s
        (X * (X * ((monicOrtho s n) ^ (2 : ℕ)).derivative + (monicOrtho s n) ^ (2 : ℕ))) =
      ((2 * n + 1 : ℕ) : ℝ) * monicOrthoAlpha s n * monicOrthoNormSq s n -
        2 * monicOrthoFirstCoeff s n * monicOrthoNormSq s n := by
  have hcomp := momentInner_monicOrtho_adaptiveOrthoNormCompanion h hn hnN
  have hodd : momentInner s (monicOrtho s n) (X * monicOrtho s n) =
      monicOrthoAlpha s n * monicOrthoNormSq s n := by
    have hnormne : monicOrthoNormSq s n ≠ 0 :=
      ne_of_gt (monicOrthoNorm_pos_below h (by omega))
    have hrawne : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 := by
      simpa only [monicOrthoNormSq] using hnormne
    rw [momentInner_comm, monicOrthoAlpha, monicOrthoNormSq,
      div_mul_cancel₀ _ hrawne]
  have hpoly :
      X * (X * ((monicOrtho s n) ^ (2 : ℕ)).derivative + (monicOrtho s n) ^ (2 : ℕ)) =
        (2 : ℝ) • (monicOrtho s n * adaptiveOrthoNormCompanion s n) +
          monicOrtho s n * (X * monicOrtho s n) := by
    have hC : C (2 : ℝ) = (2 : Polynomial ℝ) := by
      ext k
      cases k <;> simp
    simp only [pow_two, Polynomial.derivative_mul, adaptiveOrthoNormCompanion,
      Polynomial.smul_eq_C_mul]
    rw [hC]
    ring
  rw [hpoly, momentFunctional_add, momentFunctional_smul,
    ← momentInner_def, ← momentInner_def, hcomp, hodd]
  push_cast
  ring

end

end HTGeometry
