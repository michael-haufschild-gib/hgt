import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridPairSum
import GaloisForLFunctions.RHTower.Sieve.TypeIIUnswapExplicit

/-!
# Explicit hybrid Vaughan type-II block estimate

This is Babu--Sankaranarayanan's `(1/2,1/2)` type-II estimate before elementary power
simplification: actual Vaughan coefficients, effective support, harmonic loss, and curvature
conditions are all inserted.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

theorem norm_maskedBlockSum_sq_le_hybrid_bound {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B L P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQ2P : Q ≤ 2 * P) (a b : ℕ → ℝ)
    (hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ)) :
    ‖maskedBlockSum T r A B L P Q a b‖ ^ 2
      ≤ (∑ d ∈ Finset.Ico P Q, |a d| ^ 2)
        * (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
          + (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
            * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
                hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h)) := by
  refine le_trans (norm_maskedBlockSum_sq_le T r A B L P Q a b) ?_
  refine mul_le_mul_of_nonneg_left
    (pairSum_hybrid_block_le hT hr hA hB hP hQ hQ2P b hfour) ?_
  exact Finset.sum_nonneg fun d _ => sq_nonneg _

/-- Closed hybrid block estimate, with one absolute coefficient-energy constant. -/
theorem exists_norm_maskedBlockSum_sq_le_hybrid_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ P → 2 ≤ Q →
      Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖ ^ 2
        ≤ (C * (Q : ℝ) * Real.log L)
          * (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
            + typeIIShortEnergyEnvelope (effHigh B P)
              * (2 * hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q
                (effGap A B P Q))) := by
  obtain ⟨C, hC0, hClong⟩ := exists_sum_typeIILong_sq_block_le
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hP hQ hQ2P hQL h8
  have hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ) :=
    fun m hm => four_r_div_le_of_mem_effSet hA hP hQ hQ2P hr.le h8 hm
  have hmain := norm_maskedBlockSum_sq_le_hybrid_bound hT hr hA hB hP hQ hQ2P
    (fun d => typeIILong U d) (fun m => typeIIShort V m) hfour
  have hlong := sum_typeIILong_sq_block_abs_le hClong U P Q L hL hQL
  have hshort := sum_typeIIShort_sq_subset_le
    (S := effSet A B P Q L) (N := effHigh B P)
    (effSet_subset_Icc_effHigh hP hQ) V
  have hgap := sum_hybridGapCorrBound_le
    (M₀ := effLow A Q) (M₁ := effHigh B P) (P := P) (Q := Q)
    (H := effGap A B P Q) hT hr (one_le_effLow A Q) hP
  have hshort' : (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ 2)
      ≤ typeIIShortEnergyEnvelope (effHigh B P) := by
    simpa only [typeIIShortEnergyEnvelope] using hshort
  have hgap0 : 0 ≤ (∑ h ∈ Finset.Icc 1 (effGap A B P Q),
      hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h) :=
    Finset.sum_nonneg fun h _ =>
      hybridGapCorrBound_nonneg hT hr (effLow A Q) (effHigh B P) P Q h
  have hgapEnv0 : 0 ≤ hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q
      (effGap A B P Q) := le_trans hgap0 hgap
  have hE0 := typeIIShortEnergyEnvelope_nonneg (effHigh B P)
  have hbracket :
      (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ 2)
          + (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ 2)
            * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
              hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h))
        ≤ (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
          + typeIIShortEnergyEnvelope (effHigh B P)
            * (2 * hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q
              (effGap A B P Q))) := by
    gcongr
  have hright0 : 0 ≤ C * (Q : ℝ) * Real.log L := by
    have : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
    positivity
  have hraw0 : 0 ≤
      (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ 2)
        + (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ 2)
          * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
            hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h)) := by
    positivity
  exact hmain.trans (mul_le_mul hlong hbracket hraw0 hright0)

end

end RHTower.Sieve
