import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridBlockExplicit
import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridGapPower
import GaloisForLFunctions.RHTower.Sieve.TypeIIShortEnergyPower

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The explicit power envelope for the hybrid Type II gap sum. -/
def typeIIHybridGapPowerEnvelope (T r : ℝ) (A B P : ℕ) : ℝ :=
  1000 * Real.sqrt (T * r) * (B : ℝ) * Real.sqrt B / ((A : ℝ) * P)
    + 20 * Real.pi * (B : ℝ) ^ 2 / (T * r) * invSum B
    + (B : ℝ) / P

/-- A power-explicit square envelope for one hybrid Type II dyadic block. -/
def typeIIHybridBlockSqEnvelope (C T r : ℝ) (A B L P : ℕ) : ℝ :=
  (C * (2 * (P : ℝ)) * Real.log L)
    * (2 * ((B : ℝ) / (P : ℝ)) * typeIIPolylogEnvelope B)
    * (2 * (P : ℝ) + 2 * typeIIHybridGapPowerEnvelope T r A B P)

theorem typeIIHybridGapPowerEnvelope_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (A B P : ℕ) : 0 ≤ typeIIHybridGapPowerEnvelope T r A B P := by
  rw [typeIIHybridGapPowerEnvelope]
  have := invSum_nonneg B
  positivity

theorem typeIIHybridBlockSqEnvelope_eq_factored {C T r : ℝ} {A B L P : ℕ}
    (hP : 1 ≤ P) :
    typeIIHybridBlockSqEnvelope C T r A B L P =
      8 * C * (B : ℝ) * Real.log L * typeIIPolylogEnvelope B *
        ((P : ℝ) + typeIIHybridGapPowerEnvelope T r A B P) := by
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hP)
  rw [typeIIHybridBlockSqEnvelope]
  field_simp
  ring

/-- Closed power-form estimate for one actual Vaughan Type II block. -/
theorem exists_norm_maskedBlockSum_sq_le_hybrid_power :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ P → 2 ≤ Q →
      Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖ ^ 2
        ≤ typeIIHybridBlockSqEnvelope C T r A B L P := by
  obtain ⟨C, hC0, hmain⟩ := exists_norm_maskedBlockSum_sq_le_hybrid_explicit
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hP hQ hQ2P hQL h8
  have hbase := hmain (U := U) (V := V) hT hr hA hB hL hP hQ hQ2P hQL h8
  have hgap := hybridGapSumBound_le_power (B := B) hT hr hA hP hQ hQ2P
  have hgap' : hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q (effGap A B P Q)
      ≤ typeIIHybridGapPowerEnvelope T r A B P := by
    simpa only [typeIIHybridGapPowerEnvelope] using hgap
  have hE := typeIIShortEnergyEnvelope_effHigh_le_div hB hP
  have hQcast : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hDcast : ((Q - P : ℕ) : ℝ) ≤ 2 * (P : ℝ) := by
    exact_mod_cast le_trans (Nat.sub_le Q P) hQ2P
  have hlog0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have hgap0 := typeIIHybridGapPowerEnvelope_nonneg hT hr A B P
  have hE0 := typeIIShortEnergyEnvelope_nonneg (effHigh B P)
  have hrawGap0 : 0 ≤ hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q
      (effGap A B P Q) := by
    rw [hybridGapSumBound]
    have := invSum_nonneg (effGap A B P Q)
    positivity
  have hEenv0 : 0 ≤ 2 * ((B : ℝ) / (P : ℝ)) * typeIIPolylogEnvelope B := by
    exact mul_nonneg (by positivity) (typeIIPolylogEnvelope_nonneg B)
  have hprefix : C * (Q : ℝ) * Real.log L
      ≤ C * (2 * (P : ℝ)) * Real.log L := by
    have hCQ := mul_le_mul_of_nonneg_left hQcast hC0.le
    exact mul_le_mul_of_nonneg_right hCQ hlog0
  have hbracket :
      (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
          + typeIIShortEnergyEnvelope (effHigh B P)
            * (2 * hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q
              (effGap A B P Q)))
        ≤ (2 * (P : ℝ)) * (2 * ((B : ℝ) / (P : ℝ)) * typeIIPolylogEnvelope B)
          + (2 * ((B : ℝ) / (P : ℝ)) * typeIIPolylogEnvelope B)
            * (2 * typeIIHybridGapPowerEnvelope T r A B P) := by
    have h1 := mul_le_mul hDcast hE (by positivity) (by positivity)
    have h2 := mul_le_mul hE
      (mul_le_mul_of_nonneg_left hgap' (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity) hEenv0
    nlinarith
  have hrawBracket0 : 0 ≤
      (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
        + typeIIShortEnergyEnvelope (effHigh B P)
          * (2 * hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q
            (effGap A B P Q))) := by positivity
  have hprefixEnv0 : 0 ≤ C * (2 * (P : ℝ)) * Real.log L := by positivity
  refine hbase.trans ?_
  calc
    C * (Q : ℝ) * Real.log L *
        (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
          + typeIIShortEnergyEnvelope (effHigh B P)
            * (2 * hybridGapSumBound T r (effLow A Q) (effHigh B P) P Q
              (effGap A B P Q)))
        ≤ (C * (2 * (P : ℝ)) * Real.log L)
          * ((2 * (P : ℝ)) * (2 * ((B : ℝ) / (P : ℝ)) * typeIIPolylogEnvelope B)
            + (2 * ((B : ℝ) / (P : ℝ)) * typeIIPolylogEnvelope B)
              * (2 * typeIIHybridGapPowerEnvelope T r A B P)) :=
            mul_le_mul hprefix hbracket hrawBracket0 hprefixEnv0
    _ = typeIIHybridBlockSqEnvelope C T r A B L P := by
      rw [typeIIHybridBlockSqEnvelope]
      ring

/-- Norm form of the power-explicit hybrid block estimate. -/
theorem exists_norm_maskedBlockSum_le_hybrid_power :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ P → 2 ≤ Q →
      Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖
        ≤ Real.sqrt
          (8 * C * (B : ℝ) * Real.log L * typeIIPolylogEnvelope B *
            ((P : ℝ) + typeIIHybridGapPowerEnvelope T r A B P)) := by
  obtain ⟨C, hC0, hmain⟩ := exists_norm_maskedBlockSum_sq_le_hybrid_power
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hP hQ hQ2P hQL h8
  have hsq := hmain (U := U) (V := V) hT hr hA hB hL hP hQ hQ2P hQL h8
  rw [typeIIHybridBlockSqEnvelope_eq_factored hP] at hsq
  have hE0 : 0 ≤
      8 * C * (B : ℝ) * Real.log L * typeIIPolylogEnvelope B *
        ((P : ℝ) + typeIIHybridGapPowerEnvelope T r A B P) := by
    have hlog : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
    have hgap := typeIIHybridGapPowerEnvelope_nonneg hT hr A B P
    have hpoly := typeIIPolylogEnvelope_nonneg B
    positivity
  have hsqrt := Real.sq_sqrt hE0
  nlinarith [norm_nonneg (maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
    (fun m => typeIIShort V m)), Real.sqrt_nonneg
      (8 * C * (B : ℝ) * Real.log L * typeIIPolylogEnvelope B *
        ((P : ℝ) + typeIIHybridGapPowerEnvelope T r A B P))]

end

end RHTower.Sieve
