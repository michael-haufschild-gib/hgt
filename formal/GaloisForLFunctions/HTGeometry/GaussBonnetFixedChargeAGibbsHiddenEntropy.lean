import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHiddenRealization

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The explicit hidden Gibbs state starts strictly below maximal Shannon entropy. -/
theorem egbFixedChargeAGibbsHidden_entropy_initial_strict (n : ℕ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n 0 1 (egbFixedChargeAGibbsHiddenEnergy n)) <
      (n + 3 : ℝ) * Real.log 2 := by
  have hle := egbFixedChargeAGibbsEntropy_le_maximum n 0 1 (egbFixedChargeAGibbsHiddenEnergy n)
  have hne : entropy (egbFixedChargeAGibbsMarkovPopulation n 0 1 (egbFixedChargeAGibbsHiddenEnergy n)) ≠
      (n + 3 : ℝ) * Real.log 2 := by
    intro h
    have hu := (egbFixedChargeAGibbsEntropy_maximum_iff_uniform n 0 1
      (egbFixedChargeAGibbsHiddenEnergy n)).mp h
    have hf := funext hu
    rw [egbFixedChargeAGibbsHidden_initial] at hf
    exact egbFixedChargeACriticalHiddenProbability_nonuniform n hf
  by_contra h
  apply hne
  linarith

/-- The first transition reaches the entropy maximum exactly, and every later step stays there. -/
theorem egbFixedChargeAGibbsHidden_entropy_maximum (n m : ℕ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n (m + 1) 1 (egbFixedChargeAGibbsHiddenEnergy n)) =
      (n + 3 : ℝ) * Real.log 2 := by
  rw [egbFixedChargeAGibbsHidden_finite_erasure, egbFixedChargeAGibbsEntropy_uniform]

/-- The initial hidden Gibbs state carries strictly positive relative information. -/
theorem egbFixedChargeAGibbsHidden_deficit_initial_pos (n : ℕ) :
    0 < egbFixedChargeAGibbsEntropyDeficit n 0 1 (egbFixedChargeAGibbsHiddenEnergy n) := by
  rw [egbFixedChargeAGibbsEntropyDeficit_identity]
  linarith [egbFixedChargeAGibbsHidden_entropy_initial_strict n]

/-- All relative information in the hidden Gibbs state disappears in one transition. -/
theorem egbFixedChargeAGibbsHidden_deficit_erased (n m : ℕ) :
    egbFixedChargeAGibbsEntropyDeficit n (m + 1) 1 (egbFixedChargeAGibbsHiddenEnergy n) = 0 := by
  rw [egbFixedChargeAGibbsEntropyDeficit_identity, egbFixedChargeAGibbsHidden_entropy_maximum,
    sub_self]

/-- The squared deviation observable also reaches its zero equilibrium value in finite time. -/
theorem egbFixedChargeAGibbsHidden_collision_erased (n m : ℕ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsHiddenEnergy n) = 0 := by
  apply (egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform n (m + 1) 1
    (egbFixedChargeAGibbsHiddenEnergy n)).mpr
  intro i
  rw [egbFixedChargeAGibbsHidden_finite_erasure]

/-- The first step produces a strict entropy increase from a positive nonuniform Gibbs law. -/
theorem egbFixedChargeAGibbsHidden_entropy_first_step_strict (n : ℕ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n 0 1 (egbFixedChargeAGibbsHiddenEnergy n)) <
      entropy (egbFixedChargeAGibbsMarkovPopulation n 1 1 (egbFixedChargeAGibbsHiddenEnergy n)) := by
  rw [egbFixedChargeAGibbsHidden_entropy_maximum n 0]
  exact egbFixedChargeAGibbsHidden_entropy_initial_strict n

/-- Nonuniform initial data do not imply entropy grows strictly at every subsequent time. -/
theorem egbFixedChargeAGibbsHidden_entropy_not_strictMono (n : ℕ) :
    ¬ StrictMono (fun m =>
      entropy (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsHiddenEnergy n))) := by
  intro h
  have h12 := h (show (1 : ℕ) < 2 by omega)
  dsimp only at h12
  rw [egbFixedChargeAGibbsHidden_entropy_maximum n 0,
    egbFixedChargeAGibbsHidden_entropy_maximum n 1] at h12
  linarith

end
end GaloisForLFunctions.HTGeometry
