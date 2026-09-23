import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueFirstBranch

/-!
# First-branch regime closure for the Heath--Brown sparse mean value
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- In the first Heath--Brown regime `T√N ≤ N²`, the residual square-root term is absorbed by
the diagonal `N²R²` budget. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_le_firstBranchRegime
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hN : 1 ≤ N)
    (hregime : (T : ℝ) * Real.sqrt (N : ℝ) ≤ (N : ℝ) ^ (2 : ℕ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor (heathBrownPositiveInterval N hN)
            heathBrownDenseUnitWeight t‖ ^ (2 : ℕ)) ≤
      110 * Real.pi * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        (25 * Real.pi) ^ (2 : ℕ) * (N : ℝ) *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst eta * (N : ℝ) ^ eta) ^ (2 : ℕ) *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) := by
  have hbase := integral_Icc_normSq_heathBrown_fullUnit_le_firstBranch
    A T hT hA hN heta
  have hmiddle :
      35 * Real.pi * (T : ℝ) * Real.sqrt (N : ℝ) * (A.card : ℝ) ^ (2 : ℕ) ≤
        35 * Real.pi * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) := by
    calc
      _ = (35 * Real.pi * (A.card : ℝ) ^ (2 : ℕ)) *
          ((T : ℝ) * Real.sqrt (N : ℝ)) := by ring
      _ ≤ (35 * Real.pi * (A.card : ℝ) ^ (2 : ℕ)) * (N : ℝ) ^ (2 : ℕ) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ 75 * Real.pi * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        35 * Real.pi * (T : ℝ) * Real.sqrt (N : ℝ) * (A.card : ℝ) ^ (2 : ℕ) +
        (25 * Real.pi) ^ (2 : ℕ) * (N : ℝ) *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst eta * (N : ℝ) ^ eta) ^ (2 : ℕ) *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) := hbase
    _ ≤ (75 * Real.pi * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
          35 * Real.pi * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ)) +
        (25 * Real.pi) ^ (2 : ℕ) * (N : ℝ) *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst eta * (N : ℝ) ^ eta) ^ (2 : ℕ) *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) := by
      exact add_le_add (add_le_add le_rfl hmiddle) le_rfl
    _ = _ := by ring

end

end RHTower.Sieve
