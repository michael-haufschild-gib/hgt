import GaloisForLFunctions.RHTower.Sieve.TypeIIUnswapExplicit
import GaloisForLFunctions.RHTower.Sieve.GapSums

/-!
# Polylogarithmic short-coefficient energy

The exact divisor-square energy is compressed into one explicit polynomial in `1 + log B`, while
retaining its linear dependence on block length.
-/

namespace RHTower.Sieve

noncomputable section

def typeIIPolylogEnvelope (B : ℕ) : ℝ := 1 + (1 + Real.log B) ^ 3

theorem typeIIPolylogEnvelope_nonneg (B : ℕ) : 0 ≤ typeIIPolylogEnvelope B := by
  rw [typeIIPolylogEnvelope]
  positivity

theorem typeIIShortEnergyEnvelope_le {N B : ℕ} (hB : 1 ≤ B) (hNB : N ≤ B) :
    typeIIShortEnergyEnvelope N ≤ 2 * (B : ℝ) * typeIIPolylogEnvelope B := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    rw [typeIIShortEnergyEnvelope]
    simp
    exact mul_nonneg (by positivity) (typeIIPolylogEnvelope_nonneg B)
  · have hNcast : (N : ℝ) ≤ (B : ℝ) := by exact_mod_cast hNB
    have hlog : Real.log N ≤ Real.log B :=
      Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hNB)
    have hinv : invSum N ≤ 1 + Real.log B :=
      (invSum_le_one_add_log hN).trans (by linarith)
    have hinv0 := invSum_nonneg N
    have hpow : invSum N ^ 3 ≤ (1 + Real.log B) ^ 3 := by gcongr
    rw [typeIIShortEnergyEnvelope, typeIIPolylogEnvelope]
    nlinarith [mul_le_mul hNcast hpow (by positivity) (by positivity)]

theorem typeIIShortEnergyEnvelope_effHigh_le {B P : ℕ} (hB : 1 ≤ B) :
    typeIIShortEnergyEnvelope (effHigh B P)
      ≤ 2 * (B : ℝ) * typeIIPolylogEnvelope B := by
  apply typeIIShortEnergyEnvelope_le hB
  rw [effHigh]
  exact le_trans (Nat.div_le_self _ _) (by omega)

/-- The sharp divisor-scale form of the short-side energy bound. -/
theorem typeIIShortEnergyEnvelope_effHigh_le_div {B P : ℕ} (hB : 1 ≤ B) (hP : 1 ≤ P) :
    typeIIShortEnergyEnvelope (effHigh B P)
      ≤ 2 * ((B : ℝ) / (P : ℝ)) * typeIIPolylogEnvelope B := by
  let N := effHigh B P
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hmulNat : P * N ≤ B := by
    dsimp [N, effHigh]
    exact le_trans (Nat.mul_div_le (B - 1) P) (Nat.sub_le B 1)
  have hNdiv : (N : ℝ) ≤ (B : ℝ) / (P : ℝ) := by
    rw [le_div_iff₀ hP0]
    simpa [mul_comm] using (show (P : ℝ) * (N : ℝ) ≤ (B : ℝ) by exact_mod_cast hmulNat)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [show effHigh B P = 0 by exact hN, typeIIShortEnergyEnvelope]
    simp
    exact mul_nonneg (mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg B) hP0.le))
      (typeIIPolylogEnvelope_nonneg B)
  · have hNB : N ≤ B := le_trans (Nat.div_le_self _ _) (Nat.sub_le B 1)
    have hlog : Real.log N ≤ Real.log B :=
      Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hNB)
    have hinv : invSum N ≤ 1 + Real.log B :=
      (invSum_le_one_add_log hN).trans (by linarith)
    have hinv0 := invSum_nonneg N
    have hpow : invSum N ^ 3 ≤ (1 + Real.log B) ^ 3 := by gcongr
    rw [typeIIShortEnergyEnvelope, typeIIPolylogEnvelope]
    nlinarith [mul_le_mul hNdiv hpow (by positivity) (by positivity)]

end

end RHTower.Sieve
