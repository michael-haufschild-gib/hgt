import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHiddenProbability

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Transition powers preserve constants and transport arbitrary affine profiles exactly. -/
theorem egbFixedChargeACriticalMarkov_affine_action (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) (c d : ℝ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
      (fun i => c + d * f i) = fun i => c + d *
        (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f i := by
  funext i
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re * (c + d * f j)) =
    c + d * ∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re * f j
  calc
    _ = c * (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re) +
        d * ∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re * f j := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [egbFixedChargeACriticalMarkovMatrix_pow_row_sum]; ring

/-- A strictly positive nonuniform law is sent to the uniform law after one or more transitions. -/
theorem egbFixedChargeACriticalHiddenProbability_erased (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalHiddenProbability n) =
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := by
  have hp : egbFixedChargeACriticalHiddenProbability n = fun i =>
      ((2 : ℝ) ^ (n + 3))⁻¹ +
        (egbFixedChargeACriticalHiddenScale n * ((2 : ℝ) ^ (n + 3))⁻¹) *
          egbFixedChargeACriticalHiddenProfile n i := by
    funext i
    unfold egbFixedChargeACriticalHiddenProbability
    ring
  rw [hp, egbFixedChargeACriticalMarkov_affine_action,
    egbFixedChargeACriticalHiddenProfile_erased]
  funext i
  simp

/-- The initial law is strictly different from equilibrium. -/
theorem egbFixedChargeACriticalHiddenProbability_nonuniform (n : ℕ) :
    egbFixedChargeACriticalHiddenProbability n ≠ (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := by
  intro h
  have h0 := congrFun h 0
  have hp := egbFixedChargeACriticalHiddenProbability_first_gt_uniform n
  linarith

/-- Complete erasure does not confuse the hidden initial law with a fixed point. -/
theorem egbFixedChargeACriticalHiddenProbability_not_fixed (n m : ℕ) :
    (egbFixedChargeACriticalMarkovIteratedKernel n (m + 1)).toFinitePositiveKernel.applyReal
      (egbFixedChargeACriticalHiddenProbability n) ≠ egbFixedChargeACriticalHiddenProbability n := by
  rw [egbFixedChargeACriticalHiddenProbability_erased]
  intro h
  exact egbFixedChargeACriticalHiddenProbability_nonuniform n h.symm

end
end GaloisForLFunctions.HTGeometry
