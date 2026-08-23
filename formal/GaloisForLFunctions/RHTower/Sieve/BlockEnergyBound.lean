import GaloisForLFunctions.RHTower.Sieve.BlockLongEnergy

/-!
# The type-II energy of a dyadic block, bounded

Multiplying the long-side energy of the block by the closed-form pair sum gives
`blockTypeIIEnergy` explicitly, in terms of the block endpoints, the coefficient energies and the
gap sum.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

theorem norm_typeIIShort_eq (V m : ℕ) :
    ‖((typeIIShort V m : ℝ) : ℂ)‖ = |typeIIShort V m| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- **The type-II energy of a dyadic block.** -/
theorem blockTypeIIEnergy_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B L U V j : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hP : 1 ≤ 2 ^ j) (hQ : 2 ≤ min (2 ^ (j + 1)) (L + 1)) {C : ℝ} (hC0 : 0 < C)
    (hCbound : ∀ (U P Q L : ℕ), 1 ≤ L → Q ≤ L + 1 →
      (∑ d ∈ Finset.Ico P Q, ‖((typeIILong U d : ℝ) : ℂ)‖ ^ 2)
        ≤ C * (Q : ℝ) * Real.log (L : ℝ))
    (hfour : ∀ m ∈ effSet A B (2 ^ j) (min (2 ^ (j + 1)) (L + 1)) L,
      4 * (r / m) ≤ ((2 ^ j : ℕ) : ℝ))
    (hlam : ∀ m₁ ∈ effSet A B (2 ^ j) (min (2 ^ (j + 1)) (L + 1)) L,
      ∀ m₂ ∈ effSet A B (2 ^ j) (min (2 ^ (j + 1)) (L + 1)) L,
      curvedLambda (T * |r / m₁ - r / m₂|) (((2 ^ j : ℕ)) : ℝ) ≤ 1) :
    blockTypeIIEnergy T r A B L U V j
      ≤ (C * ((min (2 ^ (j + 1)) (L + 1) : ℕ) : ℝ) * Real.log (L : ℝ))
        * (((min (2 ^ (j + 1)) (L + 1) - 2 ^ j : ℕ) : ℝ)
              * (∑ m ∈ effSet A B (2 ^ j) (min (2 ^ (j + 1)) (L + 1)) L,
                  |typeIIShort V m| ^ 2)
            + (∑ m ∈ effSet A B (2 ^ j) (min (2 ^ (j + 1)) (L + 1)) L,
                |typeIIShort V m| ^ 2)
              * (2 * ∑ h ∈ Finset.Icc 1
                  (effGap A B (2 ^ j) (min (2 ^ (j + 1)) (L + 1))),
                  gapCorrBound T r (effLow A (min (2 ^ (j + 1)) (L + 1)))
                    (effHigh B (2 ^ j)) (2 ^ j) (min (2 ^ (j + 1)) (L + 1)) h)) := by
  classical
  set P : ℕ := 2 ^ j with hPdef
  set Q : ℕ := min (2 ^ (j + 1)) (L + 1) with hQdef
  have hQL : Q ≤ L + 1 := by rw [hQdef]; exact min_le_right _ _
  have hlong := hCbound U P Q L hL hQL
  have hpair := pairSum_block_le hT hr hA hB hP hQ (fun m => typeIIShort V m) hfour hlam
  have hpairnorm : (∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
      ‖((typeIIShort V m₁ : ℝ) : ℂ)‖ * ‖((typeIIShort V m₂ : ℝ) : ℂ)‖
        * ‖∑ d ∈ Finset.Ico P Q,
            maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖)
      = ∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
          |typeIIShort V m₁| * |typeIIShort V m₂|
            * ‖∑ d ∈ Finset.Ico P Q,
                maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖ := by
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
    rw [norm_typeIIShort_eq, norm_typeIIShort_eq]
  have hlong0 : (0 : ℝ) ≤ ∑ d ∈ Finset.Ico P Q, ‖((typeIILong U d : ℝ) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun d _ => sq_nonneg _
  have hpair0 : (0 : ℝ) ≤ ∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
      ‖((typeIIShort V m₁ : ℝ) : ℂ)‖ * ‖((typeIIShort V m₂ : ℝ) : ℂ)‖
        * ‖∑ d ∈ Finset.Ico P Q,
            maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖ :=
    Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ => by positivity
  rw [blockTypeIIEnergy, ← hPdef, ← hQdef]
  rw [hpairnorm] at hpair0 ⊢
  have hCQ : (0 : ℝ) ≤ C * (Q : ℝ) * Real.log (L : ℝ) := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
    positivity
  exact mul_le_mul hlong hpair hpair0 hCQ

end

end RHTower.Sieve
