import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsDominantCollisionRate
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHellingerRatios

/-!
# Dimensionless displacement for every critical Gibbs input

The centering operator already present in the corpus supplies displacement
coordinates for every Gibbs law evolved by the critical thermal kernel
extracted from arXiv:2609.00025.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

/-- Dimensionless deviation from the invariant uniform population. -/
def egbFixedChargeAGibbsDisplacement (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) : ℝ :=
  (2 : ℝ) ^ (n + 3) *
    egbFixedChargeACriticalCenteredProfile n (egbFixedChargeAGibbsMarkovPopulation n m β E) i

/-- The centered displacement is exactly normalized population minus one. -/
theorem egbFixedChargeAGibbsDisplacement_formula (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    egbFixedChargeAGibbsDisplacement n m β E i =
      (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsMarkovPopulation n m β E i - 1 := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold egbFixedChargeAGibbsDisplacement egbFixedChargeACriticalCenteredProfile
  rw [egbFixedChargeAGibbsPopulation_uniform_mean]
  field_simp

/-- Centering makes the complete displacement mass vanish at every time. -/
theorem egbFixedChargeAGibbsDisplacement_mass_zero (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i, egbFixedChargeAGibbsDisplacement n m β E i = 0 := by
  unfold egbFixedChargeAGibbsDisplacement
  rw [← Finset.mul_sum, egbFixedChargeACriticalCenteredProfile_mass_zero, mul_zero]

/-- The displacement coordinates reconstruct the actual Gibbs population. -/
theorem egbFixedChargeAGibbsDisplacement_population (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    egbFixedChargeAGibbsMarkovPopulation n m β E i =
      (1 + egbFixedChargeAGibbsDisplacement n m β E i) / (2 : ℝ) ^ (n + 3) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [egbFixedChargeAGibbsDisplacement_formula]
  field_simp
  <;> ring

/-- Every coordinate remains strictly inside the square-root and logarithm domain. -/
theorem egbFixedChargeAGibbsDisplacement_above_neg_one (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    -1 < egbFixedChargeAGibbsDisplacement n m β E i := by
  rw [egbFixedChargeAGibbsDisplacement_formula]
  have hp := mul_pos (by positivity : (0 : ℝ) < 2 ^ (n + 3))
    (egbFixedChargeAGibbsMarkovPopulation_pos n m β E i)
  linarith

/-- Collision excess is exactly the squared displacement mass divided by the squared grid size. -/
theorem egbFixedChargeAGibbsDisplacement_collision_formula (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E =
      (∑ i, egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ)) / ((2 : ℝ) ^ (n + 3)) ^ (2 : ℕ) := by
  unfold egbFixedChargeAGibbsCollisionExcess
  simp_rw [egbFixedChargeAGibbsDisplacement_population]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every displacement coordinate converges to zero for every Gibbs landscape. -/
theorem egbFixedChargeAGibbsDisplacement_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    Tendsto (fun m => egbFixedChargeAGibbsDisplacement n m β E i) atTop (nhds 0) := by
  have hp := tendsto_pi_nhds.mp (egbFixedChargeAGibbsMarkovPopulation_limit n β E) i
  have hN : Tendsto (fun _ : ℕ => (2 : ℝ) ^ (n + 3)) atTop (nhds ((2 : ℝ) ^ (n + 3))) :=
    tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (2 : ℝ) ^ (n + 3) * ((2 : ℝ) ^ (n + 3))⁻¹ - 1 = 0 := by field_simp; norm_num
  simpa only [egbFixedChargeAGibbsDisplacement_formula, he] using (hN.mul hp).sub h1

end
end GaloisForLFunctions.HTGeometry
