import GaloisForLFunctions.RHTower.Sieve.GapSums

/-!
# The correlation bound as a function of the gap alone

The two-term second-derivative bound is increasing in the curvature scale through its first term
and decreasing through its second, so sandwiching `Y = T|r/m₁ − r/m₂|` between `T r h/M₁²` and
`T r h/M₀²` turns it into a bound depending only on the gap `h`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The two-term block bound, as a function of the curvature scale. -/
def blockPairBound (Y : ℝ) (P Q : ℕ) : ℝ :=
  2500 * Real.sqrt (Y / (36 * Real.pi * P))
    + 22 * Real.sqrt (36 * Real.pi / Y) * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ))

/-- **Monotonicity of the block bound in the curvature scale.** -/
theorem blockPairBound_mono {Y Y₁ Y₂ : ℝ} (P Q : ℕ) (hY₁ : 0 < Y₁) (hle₁ : Y₁ ≤ Y)
    (hle₂ : Y ≤ Y₂) :
    blockPairBound Y P Q
      ≤ 2500 * Real.sqrt (Y₂ / (36 * Real.pi * P))
        + 22 * Real.sqrt (36 * Real.pi / Y₁) * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hY : 0 < Y := lt_of_lt_of_le hY₁ hle₁
  have hfirst : Real.sqrt (Y / (36 * Real.pi * P)) ≤ Real.sqrt (Y₂ / (36 * Real.pi * P)) := by
    refine Real.sqrt_le_sqrt ?_
    rcases Nat.eq_zero_or_pos P with hP | hP
    · simp [hP]
    · have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
      exact div_le_div_of_nonneg_right hle₂ (by positivity)
  have hsecond : Real.sqrt (36 * Real.pi / Y) ≤ Real.sqrt (36 * Real.pi / Y₁) := by
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_left (by positivity) hY₁ hle₁
  have hQ : (0 : ℝ) ≤ Real.sqrt (((Q : ℝ)) ^ (3 : ℕ)) := Real.sqrt_nonneg _
  rw [blockPairBound]
  nlinarith [hfirst, hsecond, hQ, mul_le_mul_of_nonneg_right hsecond hQ]

/-- The gap-only correlation bound. -/
def gapCorrBound (T r : ℝ) (M₀ M₁ P Q : ℕ) (h : ℕ) : ℝ :=
  2500 * Real.sqrt (T * (r * h / (M₀ : ℝ) ^ (2 : ℕ)) / (36 * Real.pi * P))
    + 22 * Real.sqrt (36 * Real.pi / (T * (r * h / (M₁ : ℝ) ^ (2 : ℕ))))
        * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ))

theorem gapCorrBound_nonneg (T r : ℝ) (M₀ M₁ P Q h : ℕ) :
    0 ≤ gapCorrBound T r M₀ M₁ P Q h := by
  rw [gapCorrBound]
  positivity

theorem cast_natDist (m₁ m₂ : ℕ) :
    ((Nat.dist m₁ m₂ : ℕ) : ℝ) = |(m₂ : ℝ) - (m₁ : ℝ)| := by
  rcases le_total m₁ m₂ with h | h
  · rw [Nat.dist, abs_of_nonneg (by exact_mod_cast sub_nonneg.2 (by exact_mod_cast h : (m₁:ℝ) ≤ m₂))]
    have h1 : m₁ - m₂ = 0 := by omega
    rw [h1]
    push_cast [Nat.cast_sub h]
    ring
  · rw [Nat.dist, abs_of_nonpos (by
      have : ((m₂ : ℝ)) ≤ (m₁ : ℝ) := by exact_mod_cast h
      linarith)]
    have h1 : m₂ - m₁ = 0 := by omega
    rw [h1]
    push_cast [Nat.cast_sub h]
    ring

/-- **The correlation bound depends only on the gap.** -/
theorem norm_masked_correlation_gap_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q M₀ M₁ : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) {m₁ m₂ : ℕ}
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : m₁ ≠ m₂)
    (hM₀ : 1 ≤ M₀) (hlo₁ : M₀ ≤ m₁) (hlo₂ : M₀ ≤ m₂) (hhi₁ : m₁ ≤ M₁) (hhi₂ : m₂ ≤ M₁)
    (h4₁ : 4 * (r / m₁) ≤ (P : ℝ)) (h4₂ : 4 * (r / m₂) ≤ (P : ℝ))
    (hlam : curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
      ≤ gapCorrBound T r M₀ M₁ P Q (Nat.dist m₁ m₂) := by
  have hmain := norm_masked_correlation_offdiag_secondDeriv_le (Q := Q) hT hr hA hB hP hm₁ hm₂ hne
    h4₁ h4₂ hlam
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
  have hY₁ : (0 : ℝ) < T * (r * ((Nat.dist m₁ m₂ : ℕ) : ℝ) / (M₁ : ℝ) ^ (2 : ℕ)) := by positivity
  have hle₁ : T * (r * ((Nat.dist m₁ m₂ : ℕ) : ℝ) / (M₁ : ℝ) ^ (2 : ℕ)) ≤ T * |r / m₁ - r / m₂| := by
    refine mul_le_mul_of_nonneg_left ?_ hT.le
    refine le_trans (le_of_eq ?_) hlow
    rw [sq]
  have hle₂ : T * |r / m₁ - r / m₂| ≤ T * (r * ((Nat.dist m₁ m₂ : ℕ) : ℝ) / (M₀ : ℝ) ^ (2 : ℕ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hT.le
    refine le_trans hhigh (le_of_eq ?_)
    rw [sq]
  refine le_trans hmain ?_
  have hmono := blockPairBound_mono P Q hY₁ hle₁ hle₂
  rw [blockPairBound] at hmono
  rw [gapCorrBound]
  exact hmono

end

end RHTower.Sieve
