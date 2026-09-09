import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsMarkovPopulation

/-!
Exact action and uniform-refresh identities for finite Gibbs populations transported
by the critical kernel of arXiv:2609.00025. These supply concrete probability
inputs to the corpus's information inequalities.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Before transport, the population is exactly the existing corpus Gibbs state. -/
theorem egbFixedChargeAGibbsMarkovPopulation_zero
    (n : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n 0 β E = _root_.HTGeometry.finiteGibbsStateWeight β E :=
  egbFixedChargeACriticalMarkovIteratedKernel_zero n _

/-- Successive blocks of transitions act on the existing transported population. -/
theorem egbFixedChargeAGibbsMarkovPopulation_add
    (n a b : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n (a + b) β E =
      (egbFixedChargeACriticalMarkovIteratedKernel n a).toFinitePositiveKernel.applyReal
        (egbFixedChargeAGibbsMarkovPopulation n b β E) :=
  egbFixedChargeACriticalMarkovIteratedKernel_add n a b _

/-- The population evolution is one application of the same Markov kernel at each step. -/
theorem egbFixedChargeAGibbsMarkovPopulation_step
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 1) β E =
      (egbFixedChargeACriticalMarkovKernel n).toFinitePositiveKernel.applyReal
        (egbFixedChargeAGibbsMarkovPopulation n m β E) :=
  egbFixedChargeACriticalMarkovIteratedKernel_step n m _

/-- Every two steps refresh one sixth of the probability uniformly. -/
theorem egbFixedChargeAGibbsMarkovPopulation_refresh
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 2) β E =
      fun i => 1 / (6 * (2 : ℝ) ^ (n + 3)) + (5 / 6) *
        (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel.applyReal
          (egbFixedChargeAGibbsMarkovPopulation n m β E) i := by
  rw [show m + 2 = 2 + m by omega, egbFixedChargeAGibbsMarkovPopulation_add,
    egbFixedChargeACriticalMarkovRefresh_action, egbFixedChargeAGibbsMarkovPopulation_mass]
  simp only [mul_one]

/-- Every transported finite Gibbs probability has the same explicit positive two-step floor. -/
theorem egbFixedChargeAGibbsMarkovPopulation_two_step_floor
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    1 / (6 * (2 : ℝ) ^ (n + 3)) ≤ egbFixedChargeAGibbsMarkovPopulation n (m + 2) β E i := by
  rw [egbFixedChargeAGibbsMarkovPopulation_refresh]
  have h := FinitePositiveKernel.applyReal_nonneg
    (egbFixedChargeACriticalMarkovRefreshKernel n).toFinitePositiveKernel
    (egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E) i
  linarith

end

end GaloisForLFunctions.HTGeometry
