import GaloisForLFunctions.RHTower.Sieve.EffectivePairRestriction

/-!
# The type-II pair sum in closed form

Restricting to the effective set, splitting off the diagonal and applying the gap-grouped
off-diagonal total gives the pair sum of a dyadic block entirely in terms of the coefficient
energy, the block length, and the gap sums.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The diagonal of the pair sum. -/
theorem diag_pair_sum_le' (T r : ℝ) (A B P Q : ℕ) (S : Finset ℕ) (b : ℕ → ℝ) :
    (∑ m ∈ S, |b m| * |b m|
        * ‖∑ d ∈ Finset.Ico P Q,
            maskedNdExp T r A B d m * (starRingEnd ℂ) (maskedNdExp T r A B d m)‖)
      ≤ ((Q - P : ℕ) : ℝ) * ∑ m ∈ S, |b m| ^ (2 : ℕ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcorr := norm_masked_correlation_diag_le T r A B P Q m
  have hnn : (0 : ℝ) ≤ |b m| * |b m| := by positivity
  have hid : ((Q - P : ℕ) : ℝ) * |b m| ^ (2 : ℕ) = (|b m| * |b m|) * ((Q - P : ℕ) : ℝ) := by ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hcorr hnn

/-- **The type-II pair sum of a dyadic block, in closed form.** -/
theorem pairSum_closed_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B P Q L M₀ M₁ H : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hM₀ : 1 ≤ M₀)
    (b : ℕ → ℝ)
    (hS : ∀ m ∈ effSet A B P Q L, 1 ≤ m ∧ M₀ ≤ m ∧ m ≤ M₁)
    (hH : ∀ m₁ ∈ effSet A B P Q L, ∀ m₂ ∈ (effSet A B P Q L).erase m₁,
      Nat.dist m₁ m₂ ∈ Finset.Icc 1 H)
    (hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ))
    (hlam : ∀ m₁ ∈ effSet A B P Q L, ∀ m₂ ∈ effSet A B P Q L,
      curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    (∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
        |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
          maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      ≤ ((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |b m| ^ (2 : ℕ))
        + (∑ m ∈ effSet A B P Q L, |b m| ^ (2 : ℕ))
          * (2 * ∑ h ∈ Finset.Icc 1 H, gapCorrBound T r M₀ M₁ P Q h) := by
  classical
  rw [pair_sum_restrict_eff hA hB hP T r b,
    sum_pair_split (effSet A B P Q L)
      (fun m₁ m₂ => |b m₁| * |b m₂| * ‖∑ d ∈ Finset.Ico P Q,
        maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)]
  have hdiag := diag_pair_sum_le' T r A B P Q (effSet A B P Q L) b
  have hoff := offdiag_correlation_total_le (Q := Q) hT hr hA hB hP hM₀ (effSet A B P Q L) b hS hH
    hfour hlam
  linarith [hdiag, hoff]

end

end RHTower.Sieve
