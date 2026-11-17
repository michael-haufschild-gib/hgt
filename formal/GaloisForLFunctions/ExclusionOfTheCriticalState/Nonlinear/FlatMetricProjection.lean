import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralDescent
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralRoot

/-!
# Gradient descent selects the nearest energy minimizer

The negative-part limit is the metric projection onto the entire zero-energy
cone. Its variational inequality gives a Pythagorean bound and uniqueness
of the closest minimizer, on an arbitrary measure space.
-/

open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Negative-part clipping lands in the zero-energy cone. -/
theorem negativePartLp_energy_zero (f : Lp ℝ 2 μ) :
    integralEnergy (negativePartLp f) = 0 := by
  apply (integralEnergy_zero_iff _).mpr
  filter_upwards [negativePartLp_ae f] with x hx
  rw [hx]
  exact min_le_right _ _

private theorem projection_variational (f g : Lp ℝ 2 μ)
    (hg : integralEnergy g = 0) :
    inner ℝ (f - negativePartLp f) (g - negativePartLp f) ≤ 0 := by
  rw [L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [Lp.coeFn_sub f (negativePartLp f),
    Lp.coeFn_sub g (negativePartLp f), negativePartLp_ae f,
    (integralEnergy_zero_iff g).mp hg] with x hf hd hp hgx
  rw [hf, hd]
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [hp]
  change (g x - min (f x) 0) * (f x - min (f x) 0) ≤ 0
  by_cases hx : f x ≤ 0
  · rw [min_eq_left hx, sub_self, mul_zero]
  · rw [min_eq_right (le_of_not_ge hx), sub_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hgx (le_of_not_ge hx)

/-- Squared distance to any minimizer dominates both orthogonal displacements. -/
theorem negativePartLp_pythagorean (f g : Lp ℝ 2 μ) :
    integralEnergy g = 0 →
      ‖f - negativePartLp f‖ ^ 2 + ‖g - negativePartLp f‖ ^ 2 ≤ ‖f - g‖ ^ 2 := by
  intro hg
  have he : f - g = (f - negativePartLp f) - (g - negativePartLp f) := by abel
  rw [he, norm_sub_sq_real (f - negativePartLp f) (g - negativePartLp f)]
  linarith only [projection_variational f g hg]

/-- The distance to the entire energy-minimizer set is attained by negative-part clipping. -/
theorem negativePartLp_nearest (f : Lp ℝ 2 μ) :
    IsLeast {r : ℝ | ∃ g : Lp ℝ 2 μ, integralEnergy g = 0 ∧ ‖f - g‖ = r}
      ‖f - negativePartLp f‖ := by
  constructor
  · exact ⟨negativePartLp f, negativePartLp_energy_zero f, rfl⟩
  · rintro r ⟨g, hg, rfl⟩
    have h := negativePartLp_pythagorean f g hg
    nlinarith only [h, sq_nonneg ‖g - negativePartLp f‖,
      norm_nonneg (f - negativePartLp f), norm_nonneg (f - g)]

/-- No other minimizer can be as close to the starting profile as the descent limit. -/
theorem negativePartLp_unique_nearest (f g : Lp ℝ 2 μ) :
    (integralEnergy g = 0 ∧ ‖f - g‖ ≤ ‖f - negativePartLp f‖) ↔
      g = negativePartLp f := by
  constructor
  · rintro ⟨hg, hd⟩
    have h := negativePartLp_pythagorean f g hg
    have hz : ‖g - negativePartLp f‖ = 0 := by
      nlinarith only [h, hd, norm_nonneg (f - g),
        norm_nonneg (f - negativePartLp f), norm_nonneg (g - negativePartLp f)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · rintro rfl
    exact ⟨negativePartLp_energy_zero f, le_refl _⟩

/-- Strong gradient descent converges to the unique nearest zero-energy profile. -/
theorem descentLp_tendsto_unique_nearest (f : Lp ℝ 2 μ) :
    ∃ g : Lp ℝ 2 μ,
      Tendsto (fun n : ℕ => descentLp^[n] f) atTop (𝓝 g) ∧
      integralEnergy g = 0 ∧
      ∀ h : Lp ℝ 2 μ, (integralEnergy h = 0 ∧ ‖f - h‖ ≤ ‖f - g‖) ↔ h = g :=
  ⟨negativePartLp f, descentLp_tendsto_negativePart f, negativePartLp_energy_zero f,
    negativePartLp_unique_nearest f⟩

#print axioms negativePartLp_pythagorean
#print axioms negativePartLp_nearest
#print axioms negativePartLp_unique_nearest
#print axioms descentLp_tendsto_unique_nearest
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
