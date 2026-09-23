import GaloisForLFunctions.RHTower.Sieve.TypeIIDyadicConditions
import GaloisForLFunctions.RHTower.Sieve.BlockEnergyBound

/-!
# Explicit long-orientation type-II block bound

This inserts the actual Vaughan coefficients, their proved energy bounds, the dyadic gap sum, and
the numeric curvature discharge into the long-orientation Cauchy--Schwarz estimate.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- Uniform envelope for the short Vaughan coefficient energy on an initial segment. -/
def typeIIShortEnergyEnvelope (N : ℕ) : ℝ :=
  2 * (N : ℝ) + 2 * ((N : ℝ) * invSum N ^ (3 : ℕ))

/-- Explicit gap envelope in the long orientation. -/
def typeIIUnswapGapEnvelope (T r : ℝ) (A B P : ℕ) : ℝ :=
  500 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P)
    + 1500 * (B : ℝ) * Real.sqrt B / Real.sqrt (T * r)

theorem typeIIShortEnergyEnvelope_nonneg (N : ℕ) : 0 ≤ typeIIShortEnergyEnvelope N := by
  rw [typeIIShortEnergyEnvelope]
  have := invSum_nonneg N
  positivity

theorem typeIIUnswapGapEnvelope_nonneg (T r : ℝ) (A B P : ℕ) :
    0 ≤ typeIIUnswapGapEnvelope T r A B P := by
  rw [typeIIUnswapGapEnvelope]
  positivity

/-- Closed explicit long-orientation estimate, with one absolute coefficient-energy constant. -/
theorem exists_norm_maskedBlockSum_sq_le_unswap_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ P → 2 ≤ Q →
      Q ≤ 2 * P → Q ≤ L + 1 → P < B → 8 * r ≤ (A : ℝ) →
      T * r ≤ 9 * Real.pi * A * P ^ (2 : ℕ) →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖ ^ (2 : ℕ)
        ≤ (C * (Q : ℝ) * Real.log L)
          * (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
            + typeIIShortEnergyEnvelope (effHigh B P)
              * (2 * typeIIUnswapGapEnvelope T r A B P)) := by
  obtain ⟨C, hC0, hClong⟩ := exists_sum_typeIILong_sq_block_le
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hP hQ hQ2P hQL hPB h8 hTr
  have hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ) :=
    fun m hm => four_r_div_le_of_mem_effSet hA hP hQ hQ2P hr.le h8 hm
  have hlam : ∀ m₁ ∈ effSet A B P Q L, ∀ m₂ ∈ effSet A B P Q L,
      curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1 :=
    fun m₁ hm₁ m₂ hm₂ => curvedLambda_effSet_le_one hT hA hP hQ hQ2P hr.le hTr hm₁ hm₂
  have hmain := norm_maskedBlockSum_sq_le_bound hT hr hA hB hP hQ
    (fun d => typeIILong U d) (fun m => typeIIShort V m) hfour hlam
  have hlong := sum_typeIILong_sq_block_abs_le hClong U P Q L hL hQL
  have hshort := sum_typeIIShort_sq_subset_le
    (S := effSet A B P Q L) (N := effHigh B P)
    (effSet_subset_Icc_effHigh hP hQ) V
  have hM₁ : 1 ≤ effHigh B P := by
    rw [effHigh, Nat.one_le_div_iff (by omega : 0 < P)]
    omega
  have hgap := (sum_gapCorrBound_le' hT hr (one_le_effLow A Q) hM₁).trans
    (gapSumBound_le_unswap hT hr hA hP hQ hQ2P)
  have hshort' : (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
      ≤ typeIIShortEnergyEnvelope (effHigh B P) := by
    simpa only [typeIIShortEnergyEnvelope] using hshort
  have hgap' : (∑ h ∈ Finset.Icc 1 (effGap A B P Q),
      gapCorrBound T r (effLow A Q) (effHigh B P) P Q h)
      ≤ typeIIUnswapGapEnvelope T r A B P := by
    simpa only [typeIIUnswapGapEnvelope] using hgap
  have hgap0 : 0 ≤ (∑ h ∈ Finset.Icc 1 (effGap A B P Q),
      gapCorrBound T r (effLow A Q) (effHigh B P) P Q h) :=
    Finset.sum_nonneg fun h _ => gapCorrBound_nonneg T r (effLow A Q) (effHigh B P) P Q h
  have hE0 := typeIIShortEnergyEnvelope_nonneg (effHigh B P)
  have hG0 := typeIIUnswapGapEnvelope_nonneg T r A B P
  have hbracket :
      (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
          + (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
            * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
              gapCorrBound T r (effLow A Q) (effHigh B P) P Q h))
        ≤ (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
          + typeIIShortEnergyEnvelope (effHigh B P)
            * (2 * typeIIUnswapGapEnvelope T r A B P)) := by
    gcongr
  have hright0 : 0 ≤ C * (Q : ℝ) * Real.log L := by
    have : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
    positivity
  have hraw0 : 0 ≤
      (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
        + (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
          * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
            gapCorrBound T r (effLow A Q) (effHigh B P) P Q h)) := by
    positivity
  exact hmain.trans (mul_le_mul hlong hbracket hraw0 hright0)

end

end RHTower.Sieve
