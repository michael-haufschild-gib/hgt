import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueFirstBranchRegime

/-!
# Published first regime for the Heath--Brown sparse mean value
-/

namespace RHTower.Sieve

/-- The paper's first regime `T^(2/3) ≤ N` implies the exact algebraic condition used by the
first-branch estimate. -/
theorem heathBrown_firstBranchRegime_of_twoThirds
    {T : ℝ} (hT : 0 ≤ T) {N : ℕ}
    (hregime : T ^ (2 / 3 : ℝ) ≤ (N : ℝ)) :
    T * Real.sqrt (N : ℝ) ≤ (N : ℝ) ^ 2 := by
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmono :
      (T ^ (2 / 3 : ℝ)) ^ (3 : ℝ) ≤ (N : ℝ) ^ (3 : ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hT _) hregime (by norm_num)
  have hT2 : T ^ (2 : ℕ) ≤ (N : ℝ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast T 2, ← Real.rpow_natCast (N : ℝ) 3]
    calc
      T ^ (2 : ℝ) = (T ^ (2 / 3 : ℝ)) ^ (3 : ℝ) := by
        rw [← Real.rpow_mul hT]
        norm_num
      _ ≤ (N : ℝ) ^ (3 : ℝ) := hmono
  have hmul := mul_le_mul_of_nonneg_right hT2 hN0
  have hsqN := Real.sq_sqrt hN0
  have hsq :
      (T * Real.sqrt (N : ℝ)) ^ 2 ≤ (((N : ℝ) ^ 2) ^ 2) := by
    calc
      (T * Real.sqrt (N : ℝ)) ^ 2 = T ^ 2 * (N : ℝ) := by
        rw [mul_pow, hsqN]
      _ ≤ (N : ℝ) ^ 3 * (N : ℝ) := hmul
      _ = ((N : ℝ) ^ 2) ^ 2 := by ring
  have hleft : 0 ≤ T * Real.sqrt (N : ℝ) :=
    mul_nonneg hT (Real.sqrt_nonneg _)
  have hright : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  nlinarith

open MeasureTheory

/-- First Heath--Brown branch under the paper's published condition `T^(2/3) ≤ N`. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_le_firstBranchPublishedRegime
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hN : 1 ≤ N)
    (hregime : (T : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor (heathBrownPositiveInterval N hN)
            heathBrownDenseUnitWeight t‖ ^ 2) ≤
      110 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        (25 * Real.pi) ^ 2 * (N : ℝ) *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst eta * (N : ℝ) ^ eta) ^ 2 *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) := by
  apply integral_Icc_normSq_heathBrown_fullUnit_le_firstBranchRegime
    A T hT hA hN
  · exact heathBrown_firstBranchRegime_of_twoThirds T.property.le hregime
  · exact heta

end RHTower.Sieve
