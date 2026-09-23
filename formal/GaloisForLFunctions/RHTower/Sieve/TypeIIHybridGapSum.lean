import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridGapBound
import GaloisForLFunctions.RHTower.Sieve.GapSums

/-!
# Summed hybrid type-II gap bound

The growing part costs `H√H`; the full reciprocal part costs the harmonic sum `H_H`; and the
unit remainder costs exactly `H`.  This is the summed form needed for Babu--Sankaranarayanan's
type-II estimate.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- Closed-form sum of the hybrid gap envelope. -/
def hybridGapSumBound (T r : ℝ) (M₀ M₁ P Q H : ℕ) : ℝ :=
  5000 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
      * ((H : ℝ) * Real.sqrt H)
    + (75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * (M₁ : ℝ) ^ (2 : ℕ) / (16 * T * r)) * invSum H
    + (H : ℝ)

theorem hybridGapCorrBound_split {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {M₀ M₁ P Q h : ℕ} (hM₀ : 1 ≤ M₀) (hP : 1 ≤ P) (hh : 1 ≤ h) :
    hybridGapCorrBound T r M₀ M₁ P Q h
      = 5000 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) * Real.sqrt h
        + (75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * (M₁ : ℝ) ^ (2 : ℕ) / (16 * T * r)) * (1 / (h : ℝ))
        + 1 := by
  have hM₀0 : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have harg : T * (r * (h : ℝ) / (M₀ : ℝ) ^ (2 : ℕ)) / (36 * Real.pi * P)
      = (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) * h := by
    field_simp
  have hrec : 75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * (M₁ : ℝ) ^ (2 : ℕ) / (16 * T * r * h)
      = (75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * (M₁ : ℝ) ^ (2 : ℕ) / (16 * T * r)) * (1 / h) := by
    field_simp
  rw [hybridGapCorrBound, harg, Real.sqrt_mul (by positivity), hrec]
  ring

/-- Exact hybrid gap sum, retaining the harmonic factor explicitly. -/
theorem sum_hybridGapCorrBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {M₀ M₁ P Q H : ℕ} (hM₀ : 1 ≤ M₀) (hP : 1 ≤ P) :
    (∑ h ∈ Finset.Icc 1 H, hybridGapCorrBound T r M₀ M₁ P Q h)
      ≤ hybridGapSumBound T r M₀ M₁ P Q H := by
  set C₁ : ℝ := 5000 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) with hC₁
  set C₂ : ℝ := 75 * Real.pi * (Q : ℝ) ^ (2 : ℕ) * (M₁ : ℝ) ^ (2 : ℕ) / (16 * T * r) with hC₂
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hsplit : (∑ h ∈ Finset.Icc 1 H, hybridGapCorrBound T r M₀ M₁ P Q h)
      = C₁ * (∑ h ∈ Finset.Icc 1 H, Real.sqrt h)
        + C₂ * invSum H + (H : ℝ) := by
    rw [invSum, Finset.mul_sum, Finset.mul_sum]
    have hterm : ∀ h ∈ Finset.Icc 1 H,
        hybridGapCorrBound T r M₀ M₁ P Q h
          = C₁ * Real.sqrt h + C₂ * ((1 : ℝ) / h) + 1 := by
      intro h hh
      rw [Finset.mem_Icc] at hh
      simpa only [hC₁, hC₂] using hybridGapCorrBound_split hT hr hM₀ hP hh.1
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : ((H + 1 - 1 : ℕ) : ℝ) = (H : ℝ) := by push_cast; ring
    rw [hcard]
    ring
  rw [hsplit, hybridGapSumBound, ← hC₁, ← hC₂]
  have hsqrt := sum_sqrt_le H
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hC₁0]

end

end RHTower.Sieve
