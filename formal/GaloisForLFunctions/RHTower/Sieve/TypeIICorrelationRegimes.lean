import GaloisForLFunctions.RHTower.Sieve.TypeIIMaskedEnergy
import GaloisForLFunctions.RHTower.Sieve.DifferencePhaseKuzminLandau

/-!
# The two regimes of a type-II correlation

A correlation sum attached to a pair `(m₁, m₂)` is a difference-phase sum at scale
`Y = T|r/m₁ − r/m₂|`.  Below the first-derivative resonance Kuzmin--Landau gives `≪ B²/Y`; above
it the second-derivative test gives `≪ √(Y/A) + √(B³/Y)`.  The diagonal is trivial.
-/

namespace RHTower.Sieve

open Finset RHTower Complex

noncomputable section

/-- The diagonal masked correlation is at most the length of the outer range. -/
theorem norm_masked_correlation_diag_le (T r : ℝ) (A B P Q : ℕ) (m : ℕ) :
    ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m * (starRingEnd ℂ) (maskedNdExp T r A B d m)‖
      ≤ ((Q - P : ℕ) : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ Finset.Ico P Q,
      ‖maskedNdExp T r A B d m * (starRingEnd ℂ) (maskedNdExp T r A B d m)‖ ≤ 1 := by
    intro d _
    rw [norm_mul, RCLike.norm_conj, maskedNdExp]
    split_ifs with h
    · rw [norm_ndExp]
      norm_num
    · simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]

/-- **The correlation below the first-derivative resonance.** -/
theorem norm_sum_ndExp_corr_kuzminLandau_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {m₁ m₂ A B : ℕ} (hm₁ : 1 ≤ m₁) (hm : m₁ < m₂) (hA : 1 ≤ A) (hAB : A < B)
    (h4 : 4 * (r / m₁) ≤ (A : ℝ))
    (hsmall : T * (r / m₁ - r / m₂) / (2 * Real.pi * (A : ℝ) ^ 2) ≤ 1 / 2) :
    ‖∑ d ∈ Finset.Ico A B, ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d)‖
      ≤ 75 * Real.pi * (B : ℝ) ^ 2 / (16 * (T * (r / m₁ - r / m₂))) + 1 := by
  have hm₁0 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have hm₂0 : (0 : ℝ) < (m₂ : ℝ) := by
    have : 1 ≤ m₂ := by omega
    exact_mod_cast this
  have hlt : (m₁ : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm
  have hs₂0 : (0 : ℝ) ≤ r / m₂ := by positivity
  have hslt : r / m₂ < r / m₁ := by
    rw [div_lt_div_iff₀ hm₂0 hm₁0]
    nlinarith [hr, hlt]
  simp only [ndExp]
  rw [sum_correlation_eq]
  exact norm_curvedSum_diffPhase_kuzminLandau hT hs₂0 hslt hA hAB h4 hsmall

/-- **The correlation below the resonance, in either order of the pair.** -/
theorem norm_sum_ndExp_corr_kuzminLandau_abs_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {m₁ m₂ A B : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : m₁ ≠ m₂) (hA : 1 ≤ A) (hAB : A < B)
    (h4₁ : 4 * (r / m₁) ≤ (A : ℝ)) (h4₂ : 4 * (r / m₂) ≤ (A : ℝ))
    (hsmall : T * |r / m₁ - r / m₂| / (2 * Real.pi * (A : ℝ) ^ 2) ≤ 1 / 2) :
    ‖∑ d ∈ Finset.Ico A B, ndExp T r m₁ d * (starRingEnd ℂ) (ndExp T r m₂ d)‖
      ≤ 75 * Real.pi * (B : ℝ) ^ 2 / (16 * (T * |r / m₁ - r / m₂|)) + 1 := by
  have hm₁0 : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
  have hm₂0 : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcast : (m₁ : ℝ) < (m₂ : ℝ) := by exact_mod_cast hlt
    have hslt : r / m₂ < r / m₁ := by
      rw [div_lt_div_iff₀ hm₂0 hm₁0]
      nlinarith [hr, hcast]
    have habs : |r / m₁ - r / m₂| = r / m₁ - r / m₂ := abs_of_pos (by linarith)
    rw [habs] at hsmall ⊢
    exact norm_sum_ndExp_corr_kuzminLandau_le hT hr hm₁ hlt hA hAB h4₁ hsmall
  · have hcast : (m₂ : ℝ) < (m₁ : ℝ) := by exact_mod_cast hgt
    have hslt : r / m₁ < r / m₂ := by
      rw [div_lt_div_iff₀ hm₁0 hm₂0]
      nlinarith [hr, hcast]
    have habs : |r / m₁ - r / m₂| = r / m₂ - r / m₁ := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [habs] at hsmall ⊢
    rw [sum_corr_conj, RCLike.norm_conj]
    exact norm_sum_ndExp_corr_kuzminLandau_le hT hr hm₂ hgt hA hAB h4₂ hsmall

end

end RHTower.Sieve
