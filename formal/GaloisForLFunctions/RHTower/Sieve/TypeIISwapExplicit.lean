import GaloisForLFunctions.RHTower.Sieve.TypeIIUnswapExplicit

/-!
# Explicit exchanged-orientation type-II block bound

This is the complementary small-dyadic-scale estimate.  Every phase condition and coefficient
energy is discharged, leaving only explicit inequalities in the block parameters.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- Explicit gap envelope in the exchanged orientation. -/
def typeIISwapGapEnvelope (T r : ℝ) (A B P : ℕ) : ℝ :=
  350 * (P : ℝ) * Real.sqrt (T * r) / Real.sqrt A
    + 3000 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r)

theorem typeIISwapGapEnvelope_nonneg (T r : ℝ) (A B P : ℕ) :
    0 ≤ typeIISwapGapEnvelope T r A B P := by
  rw [typeIISwapGapEnvelope]
  positivity

/-- Closed explicit exchanged-orientation estimate, under its numeric curvature threshold. -/
theorem exists_norm_maskedBlockSum_sq_le_swap_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ P → 2 ≤ Q →
      Q ≤ 2 * P → Q ≤ L + 1 → B - 1 ≤ L → P ≤ B → 8 * r ≤ (A : ℝ) →
      4 * T * r * P ^ 2 ≤ 9 * Real.pi * A ^ 3 →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖ ^ 2
        ≤ typeIIShortEnergyEnvelope (effHigh B P)
          * ((((effHigh B P + 1 - effLow A Q : ℕ) : ℝ) * (C * (Q : ℝ) * Real.log L))
            + (C * (Q : ℝ) * Real.log L) * (2 * typeIISwapGapEnvelope T r A B P)) := by
  obtain ⟨C, hC0, hClong⟩ := exists_sum_typeIILong_sq_block_le
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hP hQ hQ2P hQL hBL hPB h8 hTrP
  have hfour : ∀ d ∈ Finset.Ico P Q,
      4 * (r / d) ≤ ((effLow A Q : ℕ) : ℝ) :=
    fun d hd => four_r_div_le_effLow_of_mem_Ico hA hP hQ hQ2P hr.le h8 hd
  have hlam : ∀ d₁ ∈ Finset.Ico P Q, ∀ d₂ ∈ Finset.Ico P Q,
      curvedLambda (T * |r / d₁ - r / d₂|) ((effLow A Q : ℕ) : ℝ) ≤ 1 :=
    fun d₁ hd₁ d₂ hd₂ =>
      curvedLambda_Ico_effLow_le_one hT hA hP hQ hQ2P hr.le hTrP hd₁ hd₂
  have hmain := norm_maskedBlockSum_sq_le_swap_bound hT hr hA hB hP hQ hBL
    (fun d => typeIILong U d) (fun m => typeIIShort V m) hfour hlam
  have hlong := sum_typeIILong_sq_block_abs_le hClong U P Q L hL hQL
  have hshort := sum_typeIIShort_sq_subset_le
    (S := Finset.Ico (effLow A Q) (effHigh B P + 1)) (N := effHigh B P)
    (Ico_eff_subset_Icc_effHigh A B P Q) V
  have hM₁ : 1 ≤ Q - 1 := by omega
  have hgap := (sum_gapCorrBound_le' hT hr hP hM₁).trans
    (gapSumBound_le_swap hT hr hA hP hQ hQ2P hPB)
  have hshort' : (∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1),
      |typeIIShort V m| ^ 2) ≤ typeIIShortEnergyEnvelope (effHigh B P) := by
    simpa only [typeIIShortEnergyEnvelope] using hshort
  have hgap' : (∑ h ∈ Finset.Icc 1 (Q - 1 - P),
      gapCorrBound T r P (Q - 1) (effLow A Q) (effHigh B P + 1) h)
      ≤ typeIISwapGapEnvelope T r A B P := by
    simpa only [typeIISwapGapEnvelope] using hgap
  have hgap0 : 0 ≤ (∑ h ∈ Finset.Icc 1 (Q - 1 - P),
      gapCorrBound T r P (Q - 1) (effLow A Q) (effHigh B P + 1) h) :=
    Finset.sum_nonneg fun h _ => gapCorrBound_nonneg T r P (Q - 1)
      (effLow A Q) (effHigh B P + 1) h
  have hE0 := typeIIShortEnergyEnvelope_nonneg (effHigh B P)
  have hG0 := typeIISwapGapEnvelope_nonneg T r A B P
  have hlong0 : 0 ≤ (∑ d ∈ Finset.Ico P Q, |typeIILong U d| ^ 2) :=
    Finset.sum_nonneg fun d _ => sq_nonneg _
  have hlongEnv0 : 0 ≤ C * (Q : ℝ) * Real.log L := by
    have : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
    positivity
  have hbracket :
      ((((effHigh B P + 1 - effLow A Q : ℕ) : ℝ)
          * (∑ d ∈ Finset.Ico P Q, |typeIILong U d| ^ 2))
        + (∑ d ∈ Finset.Ico P Q, |typeIILong U d| ^ 2)
          * (2 * ∑ h ∈ Finset.Icc 1 (Q - 1 - P),
            gapCorrBound T r P (Q - 1) (effLow A Q) (effHigh B P + 1) h))
        ≤ ((((effHigh B P + 1 - effLow A Q : ℕ) : ℝ) * (C * (Q : ℝ) * Real.log L))
          + (C * (Q : ℝ) * Real.log L) * (2 * typeIISwapGapEnvelope T r A B P)) := by
    gcongr
  have hraw0 : 0 ≤
      ((((effHigh B P + 1 - effLow A Q : ℕ) : ℝ)
          * (∑ d ∈ Finset.Ico P Q, |typeIILong U d| ^ 2))
        + (∑ d ∈ Finset.Ico P Q, |typeIILong U d| ^ 2)
          * (2 * ∑ h ∈ Finset.Icc 1 (Q - 1 - P),
            gapCorrBound T r P (Q - 1) (effLow A Q) (effHigh B P + 1) h)) := by
    positivity
  exact hmain.trans (mul_le_mul hshort' hbracket hraw0 hE0)

end

end RHTower.Sieve
