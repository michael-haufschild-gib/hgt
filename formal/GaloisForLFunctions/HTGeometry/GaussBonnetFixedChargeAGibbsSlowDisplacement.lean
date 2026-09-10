import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSharpInformationExponent
import GaloisForLFunctions.HTGeometry.ParityDigitAffinityExpansion

/-!
Dimensionless slow Gibbs displacements and their exact geometric control for
the critical kernel derived from arXiv:2609.00025.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The dimensionless deviation of the slow Gibbs law from uniformity. -/
def egbFixedChargeAGibbsSlowDisplacement (n m : ℕ) (i : Fin (2 ^ (n + 3))) : ℝ :=
  egbFixedChargeAGibbsPerturbationScale n (egbFixedChargeACriticalSlowProfile n) *
    (2 / 3 : ℝ) ^ m * egbFixedChargeACriticalSlowProfile n i

/-- The dimensionless deviations have total mass zero. -/
theorem egbFixedChargeAGibbsSlowDisplacement_mass_zero (n m : ℕ) :
    ∑ i, egbFixedChargeAGibbsSlowDisplacement n m i = 0 := by
  simp only [egbFixedChargeAGibbsSlowDisplacement, ← Finset.mul_sum,
    egbFixedChargeACriticalSlowProfile_mass_zero, mul_zero]

/-- Each deviation has a pointwise geometric bound, uniform in the grid coordinate. -/
theorem egbFixedChargeAGibbsSlowDisplacement_bound (n m : ℕ) (i : Fin (2 ^ (n + 3))) :
    |egbFixedChargeAGibbsSlowDisplacement n m i| ≤ (2 / 3 : ℝ) ^ m / 2 := by
  have h := egbFixedChargeAGibbsPerturbationScale_coordinate_bound n
    (egbFixedChargeACriticalSlowProfile n) i
  rw [egbFixedChargeACriticalSlowProfile_centered] at h
  have ha : 0 ≤ (2 / 3 : ℝ) ^ m := by positivity
  calc
    _ = (2 / 3 : ℝ) ^ m * |egbFixedChargeAGibbsPerturbationScale n
        (egbFixedChargeACriticalSlowProfile n) * egbFixedChargeACriticalSlowProfile n i| := by
      unfold egbFixedChargeAGibbsSlowDisplacement
      rw [show ∀ a b c : ℝ, a * b * c = b * (a * c) by intros; ring,
        abs_mul, abs_of_nonneg ha]
    _ ≤ (2 / 3 : ℝ) ^ m * (1 / 2) := mul_le_mul_of_nonneg_left h.le ha
    _ = _ := by ring

/-- Every slow displacement stays in the interval where the existing log Taylor estimate applies. -/
theorem egbFixedChargeAGibbsSlowDisplacement_half_bound (n m : ℕ) (i : Fin (2 ^ (n + 3))) :
    |egbFixedChargeAGibbsSlowDisplacement n m i| ≤ 1 / 2 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (2 / 3 : ℝ) ≤ 1) m
  rw [one_pow] at h
  exact (egbFixedChargeAGibbsSlowDisplacement_bound n m i).trans (by linarith)

/-- The exact slow Gibbs population is the uniform mass times one plus its displacement. -/
theorem egbFixedChargeAGibbsSlowDisplacement_population (n m : ℕ) (i : Fin (2 ^ (n + 3))) :
    egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n) i =
      (1 + egbFixedChargeAGibbsSlowDisplacement n m i) / (2 : ℝ) ^ (n + 3) := by
  rw [egbFixedChargeAGibbsSlow_population]
  unfold egbFixedChargeAGibbsSlowDisplacement
  ring

end
end GaloisForLFunctions.HTGeometry
