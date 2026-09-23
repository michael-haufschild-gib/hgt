import GaloisForLFunctions.RHTower.Sieve.CorrelationGapBound

/-!
# The off-diagonal total of a dyadic block

The gap-only correlation bound splits as `C₁√h + C₂/√h`, so its gap sum is
`C₁·H√H + 2C₂√H`; feeding that through the weighted pair bound gives the off-diagonal half of the
type-II energy on one block.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem gapCorrBound_split (T r : ℝ) (M₀ M₁ P Q h : ℕ) (hT : 0 < T) (hr : 0 < r)
    (hM₀ : 1 ≤ M₀) (hM₁ : 1 ≤ M₁) (hh : 1 ≤ h) :
    gapCorrBound T r M₀ M₁ P Q h
      = 2500 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) * Real.sqrt h
        + 22 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r)) * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ))
            * (1 / Real.sqrt h) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM₀0 : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀
  have hM₁0 : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hM₁
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hfirst : Real.sqrt (T * (r * (h : ℝ) / (M₀ : ℝ) ^ (2 : ℕ)) / (36 * Real.pi * P))
      = Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) * Real.sqrt h := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rcases Nat.eq_zero_or_pos P with hP | hP
    · simp [hP]
    · have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
      field_simp
  have hsecond : Real.sqrt (36 * Real.pi / (T * (r * (h : ℝ) / (M₁ : ℝ) ^ (2 : ℕ))))
      = Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r)) * (1 / Real.sqrt h) := by
    rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [gapCorrBound, hfirst, hsecond]
  ring

/-- **The gap sum of the correlation bound.** -/
theorem sum_gapCorrBound_le (T r : ℝ) (M₀ M₁ P Q H : ℕ) (hT : 0 < T) (hr : 0 < r)
    (hM₀ : 1 ≤ M₀) (hM₁ : 1 ≤ M₁) :
    (∑ h ∈ Finset.Icc 1 H, gapCorrBound T r M₀ M₁ P Q h)
      ≤ 2500 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) * ((H : ℝ) * Real.sqrt H)
        + 22 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r)) * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ))
            * (2 * Real.sqrt H) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set C₁ : ℝ := 2500 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) with hC₁
  set C₂ : ℝ := 22 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r))
      * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ)) with hC₂
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hsplit : (∑ h ∈ Finset.Icc 1 H, gapCorrBound T r M₀ M₁ P Q h)
      = C₁ * ∑ h ∈ Finset.Icc 1 H, Real.sqrt h
        + C₂ * ∑ h ∈ Finset.Icc 1 H, 1 / Real.sqrt h := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.mem_Icc] at hh
    rw [gapCorrBound_split T r M₀ M₁ P Q h hT hr hM₀ hM₁ hh.1, hC₁, hC₂]
  rw [hsplit]
  have h1 := sum_sqrt_le H
  have h2 := sum_inv_sqrt_gap_le H
  nlinarith [mul_le_mul_of_nonneg_left h1 hC₁0, mul_le_mul_of_nonneg_left h2 hC₂0]

/-- **The off-diagonal total of a dyadic block.** -/
theorem offdiag_correlation_total_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q M₀ M₁ H : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hM₀ : 1 ≤ M₀)
    (S : Finset ℕ) (b : ℕ → ℝ)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ M₀ ≤ m ∧ m ≤ M₁)
    (hH : ∀ m₁ ∈ S, ∀ m₂ ∈ S.erase m₁, Nat.dist m₁ m₂ ∈ Finset.Icc 1 H)
    (hfour : ∀ m ∈ S, 4 * (r / m) ≤ (P : ℝ))
    (hlam : ∀ m₁ ∈ S, ∀ m₂ ∈ S,
      curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    (∑ m₁ ∈ S, ∑ m₂ ∈ S.erase m₁, |b m₁| * |b m₂|
        * ‖∑ d ∈ Finset.Ico P Q,
            maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      ≤ (∑ m ∈ S, |b m| ^ (2 : ℕ))
        * (2 * ∑ h ∈ Finset.Icc 1 H, gapCorrBound T r M₀ M₁ P Q h) := by
  classical
  have hterm : ∀ m₁ ∈ S, ∀ m₂ ∈ S.erase m₁,
      |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
        ≤ |b m₁| * |b m₂| * gapCorrBound T r M₀ M₁ P Q (Nat.dist m₁ m₂) := by
    intro m₁ hm₁ m₂ hm₂
    have hm₂S : m₂ ∈ S := Finset.mem_of_mem_erase hm₂
    have hne : m₁ ≠ m₂ := (Finset.ne_of_mem_erase hm₂).symm
    obtain ⟨h1, h2, h3⟩ := hS m₁ hm₁
    obtain ⟨h4, h5, h6⟩ := hS m₂ hm₂S
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact norm_masked_correlation_gap_le hT hr hA hB hP h1 h4 hne hM₀ h2 h5 h3 h6
      (hfour m₁ hm₁) (hfour m₂ hm₂S) (hlam m₁ hm₁ m₂ hm₂S)
  refine le_trans (Finset.sum_le_sum fun m₁ hm₁ =>
    Finset.sum_le_sum fun m₂ hm₂ => hterm m₁ hm₁ m₂ hm₂) ?_
  exact sum_offdiag_weighted_le S H b (gapCorrBound T r M₀ M₁ P Q)
    (fun h => gapCorrBound_nonneg T r M₀ M₁ P Q h) hH

end

end RHTower.Sieve
