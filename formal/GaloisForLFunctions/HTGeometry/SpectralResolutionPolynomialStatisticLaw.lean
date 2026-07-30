import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# Polynomial statistics of the spectral-resolution law

Every finite projective spectral statistic is a finite linear combination
of phase characters. Its expectation is therefore the same linear
combination of the complete Fourier law, and it converges under every
analytic spectral-resolution limit. This includes finite higher-point
spectral diagnostics after their character expansion.
-/

open Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite projective character polynomial as a continuous phase
statistic. -/
def projectiveCharacterPolynomial
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → ℂ)
    (character : J → ProjectiveCharacter d) :
    C(UnitAddTorus d, ℂ) :=
  ∑ j, coefficient j •
    UnitAddTorus.mFourier
      (finiteCharacterOfProjective (character j))

/-- Expectation of a projective character polynomial is exactly the
corresponding finite linear combination of phase-law Fourier
coefficients. -/
theorem integral_projectiveCharacterPolynomial
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → ℂ)
    (character : J → ProjectiveCharacter d)
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    (∫ x, projectiveCharacterPolynomial coefficient character x
      ∂(μ : Measure (UnitAddTorus d))) =
      ∑ j, coefficient j *
        projectivePhaseLawFourierCoefficient μ (character j) := by
  rw [projectiveCharacterPolynomial]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  rw [MeasureTheory.integral_finsetSum]
  · simp only [MeasureTheory.integral_const_mul,
      projectivePhaseLawFourierCoefficient]
  · intro j hj
    exact
      (by fun_prop :
        Continuous
          (fun x : UnitAddTorus d =>
            coefficient j *
              UnitAddTorus.mFourier
                (finiteCharacterOfProjective (character j)) x)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Every finite projective spectral polynomial converges to its
expectation under the unique spectral-resolution phase law. -/
theorem finiteAnalyticTemporalPhase_projectivePolynomial
    {d J : Type*} [Fintype d] [Fintype J]
    (omega : ℝ → d → ℝ)
    (r : ℕ) {τ : ℝ}
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ))
    (coefficient : J → ℂ)
    (character : J → ProjectiveCharacter d) :
    Tendsto
      (fun g =>
        ∫ x, projectiveCharacterPolynomial coefficient character x
          ∂(finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r) :
              Measure (UnitAddTorus d)))
      (𝓝[>] 0)
      (𝓝
        (∑ j, coefficient j *
          projectivePhaseLawFourierCoefficient μ (character j))) := by
  have h :=
    finiteAnalyticTemporalPhase_continuousStatistic
      omega r μ hμ
        (projectiveCharacterPolynomial coefficient character)
  rw [integral_projectiveCharacterPolynomial
    coefficient character μ] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
