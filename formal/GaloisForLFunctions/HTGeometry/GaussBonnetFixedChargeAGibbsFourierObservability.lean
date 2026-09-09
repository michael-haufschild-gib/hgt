import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalRealFibers

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The five Fourier coordinates of a Gibbs law that remain observable after mixing. -/
def egbFixedChargeAGibbsFourierMoment (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (k : Fin 5) : ℂ :=
  egbFixedChargeACriticalFourierCoordinates n
    (fun i => (_root_.HTGeometry.finiteGibbsStateWeight β E i : ℂ))
      (egbFixedChargeAFiveFourierModes n k)

/-- At any positive time, two Gibbs energy landscapes are indistinguishable exactly when all five retained moments agree. -/
theorem egbFixedChargeAGibbsPopulation_fiber_iff (n m : ℕ) (β γ : ℝ)
    (E F : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E =
      egbFixedChargeAGibbsMarkovPopulation n (m + 1) γ F ↔
        ∀ k : Fin 5, egbFixedChargeAGibbsFourierMoment n β E k = egbFixedChargeAGibbsFourierMoment n γ F k := by
  unfold egbFixedChargeAGibbsMarkovPopulation egbFixedChargeAGibbsFourierMoment
  exact egbFixedChargeACriticalMarkov_real_fiber_iff n m _ _

/-- Gibbs laws that remain distinct after one step cannot coincide at any later finite time. -/
theorem egbFixedChargeAGibbsPopulation_fiber_time_independent (n m : ℕ) (β γ : ℝ)
    (E F : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E =
      egbFixedChargeAGibbsMarkovPopulation n (m + 1) γ F ↔
        egbFixedChargeAGibbsMarkovPopulation n 1 β E = egbFixedChargeAGibbsMarkovPopulation n 1 γ F :=
  (egbFixedChargeAGibbsPopulation_fiber_iff n m β γ E F).trans
    (egbFixedChargeAGibbsPopulation_fiber_iff n 0 β γ E F).symm

/-- A Gibbs population reaches exact equilibrium in finite positive time iff it already does so in one step. -/
theorem egbFixedChargeAGibbsPopulation_uniform_iff_first_step (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E = (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ↔
      egbFixedChargeAGibbsMarkovPopulation n 1 β E = (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := by
  have hu (t : ℕ) :
      (egbFixedChargeACriticalMarkovIteratedKernel n t).toFinitePositiveKernel.applyReal
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) = (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := by
    have h := egbFixedChargeACriticalMarkov_affine_action n t
      (fun _ => (0 : ℝ)) (((2 : ℝ) ^ (n + 3))⁻¹) 0
    simpa only [zero_mul, add_zero] using h
  have h := egbFixedChargeACriticalMarkov_real_fiber_time_independent n m
    (_root_.HTGeometry.finiteGibbsStateWeight β E) (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹)
  rw [hu, hu] at h
  exact h

/-- Exact saturation of information capacity can happen only in the first transition. -/
theorem egbFixedChargeAGibbsEntropy_maximum_iff_first_step (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E) = (n + 3 : ℝ) * Real.log 2 ↔
      entropy (egbFixedChargeAGibbsMarkovPopulation n 1 β E) = (n + 3 : ℝ) * Real.log 2 := by
  rw [egbFixedChargeAGibbsEntropy_maximum_iff_uniform,
    egbFixedChargeAGibbsEntropy_maximum_iff_uniform]
  constructor
  · intro h i
    exact congrFun ((egbFixedChargeAGibbsPopulation_uniform_iff_first_step n m β E).mp (funext h)) i
  · intro h i
    exact congrFun ((egbFixedChargeAGibbsPopulation_uniform_iff_first_step n m β E).mpr (funext h)) i

end
end GaloisForLFunctions.HTGeometry
