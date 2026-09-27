import GaloisForLFunctions.RHTower.LogarithmicReconstructionTailSymmetry

/-!
# Testing whether stationary tail symmetry controls critical growth

An explicit comparison source has exactly the same stationary action and
continuous tail symmetry, while its normalized stationary value is `T`.
Thus those structural identities alone do not imply a square-root bound.
This is not the actual prime-deficit source and does not refute RH.
-/

noncomputable section

namespace RHTower

def logarithmicGrowingTestSource : ℝ → ℝ :=
  logarithmicDilationSum (fun t => t * Real.exp (t / 2))

theorem logarithmicReconstructionAction_growing_headExtension (v : ℕ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    logarithmicReconstructionAction
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ v) logarithmicGrowingTestSource T =
        T * Real.exp (T / 2) := by
  rw [logarithmicReconstructionAction_mobiusHeadExtension, logarithmicGrowingTestSource,
    logarithmicMobiusInverse_dilationSum _ hT]

theorem logarithmicReconstructionAction_growing_normalized (v : ℕ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(T / 2)) * logarithmicReconstructionAction
      (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ v) logarithmicGrowingTestSource T = T := by
  rw [logarithmicReconstructionAction_growing_headExtension v hT]
  have he : Real.exp (-(T / 2)) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = T * (Real.exp (-(T / 2)) * Real.exp (T / 2)) := by ring
    _ = T := by rw [he, mul_one]

theorem logarithmicReconstructionAction_growing_exceeds_every_critical_bound
    (v : ℕ → ℝ) (C : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ C * Real.exp (T / 2) <
      |logarithmicReconstructionAction
        (logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊ v) logarithmicGrowingTestSource T| := by
  let T := max C 0 + 1
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  refine ⟨T, hT, ?_⟩
  rw [logarithmicReconstructionAction_growing_headExtension v hT,
    abs_of_nonneg (mul_nonneg hT (Real.exp_pos _).le)]
  apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
  dsimp only [T]
  exact lt_add_of_le_of_pos (le_max_left C 0) zero_lt_one

end RHTower
