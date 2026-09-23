import GaloisForLFunctions.RHTower.Sieve.FibrePowerBound

/-!
# The gap sum as a single square root

Both halves of the gap sum are products of square roots, so each collapses to one square root of a
rational expression in the parameters.  In that form the substitution of the dyadic values is a
single inequality between the radicands.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The gap sum in single-square-root form. -/
def gapSumBound (T r : ℝ) (M₀ M₁ P Q H : ℕ) : ℝ :=
  2500 * Real.sqrt (T * r * (H : ℝ) ^ (3 : ℕ) / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
    + 44 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) * (Q : ℝ) ^ (3 : ℕ) * (H : ℝ) / (T * r))

theorem gapSumBound_nonneg (T r : ℝ) (M₀ M₁ P Q H : ℕ) : 0 ≤ gapSumBound T r M₀ M₁ P Q H := by
  rw [gapSumBound]; positivity

/-- **The gap sum, collapsed.** -/
theorem sum_gapCorrBound_le' {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {M₀ M₁ P Q H : ℕ}
    (hM₀ : 1 ≤ M₀) (hM₁ : 1 ≤ M₁) :
    (∑ h ∈ Finset.Icc 1 H, gapCorrBound T r M₀ M₁ P Q h)
      ≤ gapSumBound T r M₀ M₁ P Q H := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hTr : (0 : ℝ) < T * r := by positivity
  have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hbase := sum_gapCorrBound_le T r M₀ M₁ P Q H hT hr hM₀ hM₁
  have hfirst : 2500 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
      * ((H : ℝ) * Real.sqrt H)
      = 2500 * Real.sqrt (T * r * (H : ℝ) ^ (3 : ℕ) / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) := by
    have hHc : (H : ℝ) * Real.sqrt H = Real.sqrt ((H : ℝ) ^ (3 : ℕ)) := by
      rw [show ((H : ℝ)) ^ (3 : ℕ) = ((H : ℝ)) ^ (2 : ℕ) * (H : ℝ) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hH]
    have e1 : Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) * Real.sqrt ((H : ℝ) ^ (3 : ℕ))
        = Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)) * (H : ℝ) ^ (3 : ℕ)) :=
      (Real.sqrt_mul (by positivity) _).symm
    have e2 : T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)) * (H : ℝ) ^ (3 : ℕ)
        = T * r * (H : ℝ) ^ (3 : ℕ) / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)) := by ring
    calc 2500 * Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) * ((H : ℝ) * Real.sqrt H)
        = 2500 * (Real.sqrt (T * r / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P)))
            * Real.sqrt ((H : ℝ) ^ (3 : ℕ))) := by rw [hHc]; ring
      _ = 2500 * Real.sqrt (T * r * (H : ℝ) ^ (3 : ℕ) / ((M₀ : ℝ) ^ (2 : ℕ) * (36 * Real.pi * P))) := by
          rw [e1, e2]
  have hsecond : 22 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r))
      * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ)) * (2 * Real.sqrt H)
      = 44 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) * (Q : ℝ) ^ (3 : ℕ) * (H : ℝ) / (T * r)) := by
    have e1 : Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r)) * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ))
        = Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r) * ((Q : ℝ)) ^ (3 : ℕ)) :=
      (Real.sqrt_mul (by positivity) _).symm
    have e2 : Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r) * ((Q : ℝ)) ^ (3 : ℕ))
        * Real.sqrt (H : ℝ)
        = Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r) * ((Q : ℝ)) ^ (3 : ℕ) * (H : ℝ)) :=
      (Real.sqrt_mul (by positivity) _).symm
    have e3 : 36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r) * ((Q : ℝ)) ^ (3 : ℕ) * (H : ℝ)
        = 36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) * (Q : ℝ) ^ (3 : ℕ) * (H : ℝ) / (T * r) := by ring
    calc 22 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r))
          * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ)) * (2 * Real.sqrt H)
        = 44 * (Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r))
            * Real.sqrt (((Q : ℝ)) ^ (3 : ℕ)) * Real.sqrt (H : ℝ)) := by ring
      _ = 44 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) / (T * r) * ((Q : ℝ)) ^ (3 : ℕ) * (H : ℝ)) := by
          rw [e1, e2]
      _ = 44 * Real.sqrt (36 * Real.pi * (M₁ : ℝ) ^ (2 : ℕ) * (Q : ℝ) ^ (3 : ℕ) * (H : ℝ) / (T * r)) := by
          rw [e3]
  rw [gapSumBound]
  linarith [hbase, hfirst, hsecond]

end

end RHTower.Sieve
