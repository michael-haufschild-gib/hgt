import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridGapSum
import GaloisForLFunctions.RHTower.Sieve.EffectiveSetHypotheses

/-!
# Hybrid type-II pair sum

The hybrid gap envelope is inserted into the weighted off-diagonal grouping, then combined with the
exact diagonal and effective-set restriction.  This is the pair-energy form of exponent pair
`(1/2,1/2)`.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

theorem offdiag_hybrid_correlation_total_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q M₀ M₁ H : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (hQ2P : Q ≤ 2 * P) (hM₀ : 1 ≤ M₀)
    (S : Finset ℕ) (b : ℕ → ℝ)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ M₀ ≤ m ∧ m ≤ M₁)
    (hH : ∀ m₁ ∈ S, ∀ m₂ ∈ S.erase m₁, Nat.dist m₁ m₂ ∈ Finset.Icc 1 H)
    (hfour : ∀ m ∈ S, 4 * (r / m) ≤ (P : ℝ)) :
    (∑ m₁ ∈ S, ∑ m₂ ∈ S.erase m₁, |b m₁| * |b m₂|
        * ‖∑ d ∈ Finset.Ico P Q,
            maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      ≤ (∑ m ∈ S, |b m| ^ 2)
        * (2 * ∑ h ∈ Finset.Icc 1 H, hybridGapCorrBound T r M₀ M₁ P Q h) := by
  classical
  have hterm : ∀ m₁ ∈ S, ∀ m₂ ∈ S.erase m₁,
      |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖
        ≤ |b m₁| * |b m₂| * hybridGapCorrBound T r M₀ M₁ P Q (Nat.dist m₁ m₂) := by
    intro m₁ hm₁ m₂ hm₂
    have hm₂S : m₂ ∈ S := Finset.mem_of_mem_erase hm₂
    have hne : m₁ ≠ m₂ := (Finset.ne_of_mem_erase hm₂).symm
    obtain ⟨h1, h2, h3⟩ := hS m₁ hm₁
    obtain ⟨h4, h5, h6⟩ := hS m₂ hm₂S
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact norm_masked_correlation_hybrid_gap_le hT hr hA hB hP hQ2P h1 h4 hne
      hM₀ h2 h5 h3 h6 (hfour m₁ hm₁) (hfour m₂ hm₂S)
  refine le_trans (Finset.sum_le_sum fun m₁ hm₁ =>
    Finset.sum_le_sum fun m₂ hm₂ => hterm m₁ hm₁ m₂ hm₂) ?_
  exact sum_offdiag_weighted_le S H b (hybridGapCorrBound T r M₀ M₁ P Q)
    (fun h => hybridGapCorrBound_nonneg hT hr M₀ M₁ P Q h) hH

theorem pairSum_hybrid_closed_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q L M₀ M₁ H : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (hQ2P : Q ≤ 2 * P) (hM₀ : 1 ≤ M₀) (b : ℕ → ℝ)
    (hS : ∀ m ∈ effSet A B P Q L, 1 ≤ m ∧ M₀ ≤ m ∧ m ≤ M₁)
    (hH : ∀ m₁ ∈ effSet A B P Q L, ∀ m₂ ∈ (effSet A B P Q L).erase m₁,
      Nat.dist m₁ m₂ ∈ Finset.Icc 1 H)
    (hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ)) :
    (∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
        |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      ≤ ((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
        + (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
          * (2 * ∑ h ∈ Finset.Icc 1 H, hybridGapCorrBound T r M₀ M₁ P Q h) := by
  classical
  rw [pair_sum_restrict_eff hA hB hP T r b,
    sum_pair_split (effSet A B P Q L)
      (fun m₁ m₂ => |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)]
  have hdiag := diag_pair_sum_le' T r A B P Q (effSet A B P Q L) b
  have hoff := offdiag_hybrid_correlation_total_le (Q := Q) hT hr hA hB hP hQ2P hM₀
    (effSet A B P Q L) b hS hH hfour
  linarith [hdiag, hoff]

/-- Effective-set specialization of the hybrid pair sum. -/
theorem pairSum_hybrid_block_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQ2P : Q ≤ 2 * P) (b : ℕ → ℝ)
    (hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ)) :
    (∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
        |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      ≤ ((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
        + (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
          * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
              hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h) :=
  pairSum_hybrid_closed_le hT hr hA hB hP hQ2P (one_le_effLow A Q) b
    (effSet_confined hP hQ) (effSet_gap hP hQ) hfour

end

end RHTower.Sieve
