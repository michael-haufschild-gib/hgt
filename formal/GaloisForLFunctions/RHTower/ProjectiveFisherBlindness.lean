import Mathlib

/-!
# Projective Fisher blindness to unimodular Dirichlet phases

Born probabilities, their expectations, and their variance metric are unchanged by a fixed
coordinatewise unimodular phase twist.  Thus the Fisher geometry of a Dirichlet coherent state
depends on coefficient magnitudes and cannot by itself recover the zero divisor of the scalar
Dirichlet series, which also depends on coefficient phases.
-/

noncomputable section

namespace RHTower

/-- Born probability of one coordinate of a complex state. -/
def bornProbability {ι : Type*} (ψ : ι → ℂ) (i : ι) : ℝ :=
  ‖ψ i‖ ^ (2 : ℕ) / ∑' j, ‖ψ j‖ ^ (2 : ℕ)

/-- Expectation of a real observable in the Born distribution of a complex state. -/
def bornExpectation {ι : Type*} (ψ : ι → ℂ) (E : ι → ℝ) : ℝ :=
  ∑' i, bornProbability ψ i * E i

/-- Variance of a real observable in the Born distribution of a complex state. -/
def bornVariance {ι : Type*} (ψ : ι → ℂ) (E : ι → ℝ) : ℝ :=
  bornExpectation ψ (fun i => E i ^ (2 : ℕ)) - bornExpectation ψ E ^ (2 : ℕ)

/-- A coordinatewise unimodular phase twist leaves every Born probability unchanged. -/
theorem bornProbability_phase_twist {ι : Type*} (ψ u : ι → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (i : ι) :
    bornProbability (fun j => u j * ψ j) i = bornProbability ψ i := by
  unfold bornProbability
  have hterm : ∀ j, ‖u j * ψ j‖ ^ (2 : ℕ) = ‖ψ j‖ ^ (2 : ℕ) := by
    intro j
    rw [norm_mul, hu]
    simp
  rw [hterm i, tsum_congr hterm]

/-- A coordinatewise unimodular phase twist leaves all Born expectations unchanged. -/
theorem bornExpectation_phase_twist {ι : Type*} (ψ u : ι → ℂ) (E : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) :
    bornExpectation (fun j => u j * ψ j) E = bornExpectation ψ E := by
  unfold bornExpectation
  apply tsum_congr
  intro i
  rw [bornProbability_phase_twist ψ u hu i]

/-- In particular, the variance/Fisher scale is blind to all fixed unimodular coordinate phases. -/
theorem bornVariance_phase_twist {ι : Type*} (ψ u : ι → ℂ) (E : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) :
    bornVariance (fun j => u j * ψ j) E = bornVariance ψ E := by
  unfold bornVariance
  rw [bornExpectation_phase_twist ψ u (fun i => E i ^ (2 : ℕ)) hu,
    bornExpectation_phase_twist ψ u E hu]

end RHTower
