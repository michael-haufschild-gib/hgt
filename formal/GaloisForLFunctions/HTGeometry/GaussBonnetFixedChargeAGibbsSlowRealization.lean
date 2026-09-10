import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsPerturbationDynamics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A positive Gibbs state carrying precisely the slow first harmonic. -/
def egbFixedChargeAGibbsSlowEnergy (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  egbFixedChargeAGibbsPerturbationEnergy n (egbFixedChargeACriticalSlowProfile n)

/-- The slow Gibbs law has an exact formula at every finite time. -/
theorem egbFixedChargeAGibbsSlow_population (n m : ℕ) :
    egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
      fun i => ((2 : ℝ) ^ (n + 3))⁻¹ +
        (egbFixedChargeAGibbsPerturbationScale n (egbFixedChargeACriticalSlowProfile n) /
          (2 : ℝ) ^ (n + 3)) * ((2 / 3 : ℝ) ^ m * egbFixedChargeACriticalSlowProfile n i) := by
  unfold egbFixedChargeAGibbsSlowEnergy
  rw [egbFixedChargeAGibbsPerturbation_evolution, egbFixedChargeACriticalSlowProfile_centered,
    egbFixedChargeACriticalSlowProfile_evolution]

/-- The slow Gibbs population retains a strict coordinate excess at every finite time. -/
theorem egbFixedChargeAGibbsSlow_first_gt_uniform (n m : ℕ) :
    ((2 : ℝ) ^ (n + 3))⁻¹ <
      egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n) 0 := by
  rw [egbFixedChargeAGibbsSlow_population]
  dsimp only
  have hp := mul_pos
    (div_pos (egbFixedChargeAGibbsPerturbationScale_pos n (egbFixedChargeACriticalSlowProfile n))
      (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 3)))
    (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2 / 3) m) (egbFixedChargeACriticalSlowProfile_first_pos n))
  linarith

/-- This explicit Gibbs state never reaches exact equilibrium at a finite time. -/
theorem egbFixedChargeAGibbsSlow_ne_uniform (n m : ℕ) :
    egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n) ≠
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := by
  intro h
  have h0 := congrFun h 0
  have hp := egbFixedChargeAGibbsSlow_first_gt_uniform n m
  linarith

/-- The slow Gibbs state has strictly positive initial collision excess. -/
theorem egbFixedChargeAGibbsSlow_collision_initial_pos (n : ℕ) :
    0 < egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) := by
  unfold egbFixedChargeAGibbsSlowEnergy
  rw [egbFixedChargeAGibbsPerturbation_collision_initial]
  have hc := div_pos
    (egbFixedChargeAGibbsPerturbationScale_pos n (egbFixedChargeACriticalSlowProfile n))
    (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 3))
  have hs : 0 < (egbFixedChargeAGibbsPerturbationScale n (egbFixedChargeACriticalSlowProfile n) /
      (2 : ℝ) ^ (n + 3)) ^ 2 := by nlinarith
  exact mul_pos hs (egbFixedChargeACriticalSlowProfile_energy_pos n)

/-- A genuine positive Gibbs law realizes the spectral collision rate exactly. -/
theorem egbFixedChargeAGibbsSlow_collision_exact (n m : ℕ) :
    egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) =
      (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) := by
  unfold egbFixedChargeAGibbsSlowEnergy
  rw [egbFixedChargeAGibbsPerturbation_collision_identity,
    egbFixedChargeACriticalSlowProfile_energy_exact,
    egbFixedChargeAGibbsPerturbation_collision_initial]
  ring

/-- Collision excess stays strictly positive at every finite time. -/
theorem egbFixedChargeAGibbsSlow_collision_pos (n m : ℕ) :
    0 < egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsSlowEnergy n) := by
  rw [egbFixedChargeAGibbsSlow_collision_exact]
  exact mul_pos (pow_pos (by norm_num) _) (egbFixedChargeAGibbsSlow_collision_initial_pos n)

end
end GaloisForLFunctions.HTGeometry
