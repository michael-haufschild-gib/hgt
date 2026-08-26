import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridCorrelation
import GaloisForLFunctions.RHTower.Sieve.CorrelationGapBound

/-!
# Gap-only hybrid type-II correlation bound

This replaces pair-dependent reciprocal differences by the exact natural-number gap while retaining
the full reciprocal remainder supplied by the hybrid `(1/2,1/2)` estimate.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- Hybrid correlation envelope as a function only of the pair gap. -/
def hybridGapCorrBound (T r : ℝ) (M₀ M₁ P Q h : ℕ) : ℝ :=
  5000 * Real.sqrt (T * (r * h / (M₀ : ℝ) ^ 2) / (36 * Real.pi * P))
    + 75 * Real.pi * (Q : ℝ) ^ 2 * (M₁ : ℝ) ^ 2 /
      (16 * T * r * h) + 1

theorem hybridGapCorrBound_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (M₀ M₁ P Q h : ℕ) :
    0 ≤ hybridGapCorrBound T r M₀ M₁ P Q h := by
  rw [hybridGapCorrBound]
  positivity

/-- The hybrid correlation estimate depends only on the gap and enclosing interval. -/
theorem norm_masked_correlation_hybrid_gap_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q M₀ M₁ : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hQ2P : Q ≤ 2 * P)
    {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : m₁ ≠ m₂)
    (hM₀ : 1 ≤ M₀) (hlo₁ : M₀ ≤ m₁) (hlo₂ : M₀ ≤ m₂)
    (hhi₁ : m₁ ≤ M₁) (hhi₂ : m₂ ≤ M₁)
    (h4₁ : 4 * (r / m₁) ≤ (P : ℝ)) (h4₂ : 4 * (r / m₂) ≤ (P : ℝ))
    (hlam : curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
      ≤ hybridGapCorrBound T r M₀ M₁ P Q (Nat.dist m₁ m₂) := by
  have hmain := norm_masked_correlation_offdiag_hybrid_le hT hr hA hB hP hQ2P
    hm₁ hm₂ hne h4₁ h4₂ hlam
  have hM₀0 : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀
  have hM₁0 : (0 : ℝ) < (M₁ : ℝ) := lt_of_lt_of_le hM₀0 (by exact_mod_cast le_trans hlo₁ hhi₁)
  have hdist : 1 ≤ Nat.dist m₁ m₂ := by
    rcases Nat.lt_or_ge m₁ m₂ with h | h
    · rw [Nat.dist]; omega
    · have : m₂ < m₁ := by omega
      rw [Nat.dist]; omega
  have hd0 : (0 : ℝ) < ((Nat.dist m₁ m₂ : ℕ) : ℝ) := by exact_mod_cast hdist
  have hlow := le_abs_inv_diff hr.le hm₁ hm₂ hhi₁ hhi₂
  have hhigh := abs_inv_diff_le hr.le hm₁ hm₂ hM₀ hlo₁ hlo₂
  rw [← cast_natDist] at hlow hhigh
  have hY₁ : (0 : ℝ) < T * (r * ((Nat.dist m₁ m₂ : ℕ) : ℝ) / (M₁ : ℝ) ^ 2) := by positivity
  have hYlow : T * (r * ((Nat.dist m₁ m₂ : ℕ) : ℝ) / (M₁ : ℝ) ^ 2)
      ≤ T * |r / m₁ - r / m₂| := by
    apply mul_le_mul_of_nonneg_left _ hT.le
    simpa [sq] using hlow
  have hY : (0 : ℝ) < T * |r / m₁ - r / m₂| := lt_of_lt_of_le hY₁ hYlow
  have hY₂ : T * |r / m₁ - r / m₂|
      ≤ T * (r * ((Nat.dist m₁ m₂ : ℕ) : ℝ) / (M₀ : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hT.le
    simpa [sq] using hhigh
  have hfirst : Real.sqrt (T * |r / m₁ - r / m₂| / (36 * Real.pi * P))
      ≤ Real.sqrt (T * (r * ((Nat.dist m₁ m₂ : ℕ) : ℝ) / (M₀ : ℝ) ^ 2)
        / (36 * Real.pi * P)) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right hY₂ (by positivity)
  have hrec : 75 * Real.pi * (Q : ℝ) ^ 2 /
      (16 * (T * |r / m₁ - r / m₂|))
      ≤ 75 * Real.pi * (Q : ℝ) ^ 2 * (M₁ : ℝ) ^ 2 /
        (16 * T * r * (Nat.dist m₁ m₂ : ℝ)) := by
    have hden : 16 * (T * (r * (Nat.dist m₁ m₂ : ℝ) / (M₁ : ℝ) ^ 2))
        ≤ 16 * (T * |r / m₁ - r / m₂|) := by
      nlinarith [hYlow]
    have hdiv := div_le_div_of_nonneg_left
      (by positivity : (0 : ℝ) ≤ 75 * Real.pi * (Q : ℝ) ^ 2)
      (by positivity : (0 : ℝ) < 16 * (T * (r * (Nat.dist m₁ m₂ : ℝ) / (M₁ : ℝ) ^ 2))) hden
    calc
      75 * Real.pi * (Q : ℝ) ^ 2 / (16 * (T * |r / m₁ - r / m₂|))
          ≤ 75 * Real.pi * (Q : ℝ) ^ 2 /
            (16 * (T * (r * (Nat.dist m₁ m₂ : ℝ) / (M₁ : ℝ) ^ 2))) := hdiv
      _ = 75 * Real.pi * (Q : ℝ) ^ 2 * (M₁ : ℝ) ^ 2 /
            (16 * T * r * (Nat.dist m₁ m₂ : ℝ)) := by field_simp
  rw [hybridGapCorrBound]
  nlinarith [hmain, hfirst, hrec]

end

end RHTower.Sieve
