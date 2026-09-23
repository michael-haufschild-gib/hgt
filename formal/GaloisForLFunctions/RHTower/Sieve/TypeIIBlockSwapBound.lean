import GaloisForLFunctions.RHTower.Sieve.TypeIIBlockSum

/-!
# The block form estimated through the short variable

When Cauchy--Schwarz is applied to the short variable the pair sum runs over the long variable's
own block, so the confinement of the pair is immediate: the two members lie in `[P, Q)` and their
gap is at most `Q − 1 − P`.  The diagonal is then proportional to the length of the effective short
interval, which is the estimate the small blocks need.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- **The swapped pair sum in closed form.** -/
theorem swap_pairSum_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B P Q : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (a : ℕ → ℝ)
    (hfour : ∀ d ∈ Finset.Ico P Q, 4 * (r / d) ≤ ((effLow A Q : ℕ) : ℝ))
    (hlam : ∀ d₁ ∈ Finset.Ico P Q, ∀ d₂ ∈ Finset.Ico P Q,
      curvedLambda (T * |r / d₁ - r / d₂|) ((effLow A Q : ℕ) : ℝ) ≤ 1) :
    (∑ d₁ ∈ Finset.Ico P Q, ∑ d₂ ∈ Finset.Ico P Q, |a d₁| * |a d₂|
        * ‖∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1),
            maskedNdExp T r A B m d₁ * (starRingEnd ℂ) (maskedNdExp T r A B m d₂)‖)
      ≤ ((effHigh B P + 1 - effLow A Q : ℕ) : ℝ) * (∑ d ∈ Finset.Ico P Q, |a d| ^ (2 : ℕ))
        + (∑ d ∈ Finset.Ico P Q, |a d| ^ (2 : ℕ))
          * (2 * ∑ h ∈ Finset.Icc 1 (Q - 1 - P),
              gapCorrBound T r P (Q - 1) (effLow A Q) (effHigh B P + 1) h) := by
  classical
  rw [sum_pair_split (Finset.Ico P Q)
    (fun d₁ d₂ => |a d₁| * |a d₂|
      * ‖∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1),
          maskedNdExp T r A B m d₁ * (starRingEnd ℂ) (maskedNdExp T r A B m d₂)‖)]
  have hdiag := diag_pair_sum_le' T r A B (effLow A Q) (effHigh B P + 1) (Finset.Ico P Q) a
  have hS : ∀ d ∈ Finset.Ico P Q, 1 ≤ d ∧ P ≤ d ∧ d ≤ Q - 1 := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    exact ⟨le_trans hP hd.1, hd.1, by omega⟩
  have hH : ∀ d₁ ∈ Finset.Ico P Q, ∀ d₂ ∈ (Finset.Ico P Q).erase d₁,
      Nat.dist d₁ d₂ ∈ Finset.Icc 1 (Q - 1 - P) := by
    intro d₁ hd₁ d₂ hd₂
    have hd₂' : d₂ ∈ Finset.Ico P Q := Finset.mem_of_mem_erase hd₂
    have hne : d₂ ≠ d₁ := Finset.ne_of_mem_erase hd₂
    rw [Finset.mem_Ico] at hd₁ hd₂'
    rw [Finset.mem_Icc, Nat.dist]
    omega
  have hoff := offdiag_correlation_total_le (Q := effHigh B P + 1) hT hr hA hB
    (one_le_effLow A Q) hP (Finset.Ico P Q) a hS hH hfour hlam
  linarith [hdiag, hoff]

/-- **The block form, estimated through the short variable.** -/
theorem norm_maskedBlockSum_sq_le_swap_bound {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B L P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hBL : B - 1 ≤ L)
    (a b : ℕ → ℝ)
    (hfour : ∀ d ∈ Finset.Ico P Q, 4 * (r / d) ≤ ((effLow A Q : ℕ) : ℝ))
    (hlam : ∀ d₁ ∈ Finset.Ico P Q, ∀ d₂ ∈ Finset.Ico P Q,
      curvedLambda (T * |r / d₁ - r / d₂|) ((effLow A Q : ℕ) : ℝ) ≤ 1) :
    ‖maskedBlockSum T r A B L P Q a b‖ ^ (2 : ℕ)
      ≤ (∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1), |b m| ^ (2 : ℕ))
        * (((effHigh B P + 1 - effLow A Q : ℕ) : ℝ) * (∑ d ∈ Finset.Ico P Q, |a d| ^ (2 : ℕ))
          + (∑ d ∈ Finset.Ico P Q, |a d| ^ (2 : ℕ))
            * (2 * ∑ h ∈ Finset.Icc 1 (Q - 1 - P),
                gapCorrBound T r P (Q - 1) (effLow A Q) (effHigh B P + 1) h)) := by
  refine le_trans (norm_maskedBlockSum_sq_le_swap hA hB hP hQ hBL T r a b) ?_
  refine mul_le_mul_of_nonneg_left (swap_pairSum_le hT hr hA hB hP a hfour hlam) ?_
  exact Finset.sum_nonneg fun m _ => sq_nonneg _

end

end RHTower.Sieve
