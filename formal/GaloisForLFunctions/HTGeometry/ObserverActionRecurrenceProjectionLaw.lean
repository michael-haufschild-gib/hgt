import GaloisForLFunctions.HTGeometry.UniversalObserverActionLaw
import GaloisForLFunctions.HTGeometry.SpectralResolutionPolynomialStatisticLaw

/-!
# Recurrence as a projection of the observer-action law

Finite survival fidelity and the spectral form factor are quadratic
polynomials in projective phase characters.  This file identifies their
complete scaling law as a direct projection of the universal
observer-action probability law.

The result is not a separate recurrence principle: every ordered energy
gap is one projective character, and the weighted return statistic is their
finite linear combination.
-/

open Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Projective phase character selected by one ordered pair of spectral
labels. -/
def pairProjectiveCharacter
    {d : Type*} (i j : d) : ProjectiveCharacter d :=
  ⟨Finsupp.single i 1 - Finsupp.single j 1, by
    change integerCharacterCharge d
      (Finsupp.single i 1 - Finsupp.single j 1) = 0
    rw [map_sub]
    simp [integerCharacterCharge]⟩

/-- The detuning of an ordered-pair character is its energy gap. -/
theorem finiteProjectiveCharacterDetuning_pair
    {d : Type*} [Fintype d]
    (omega : d → ℝ) (i j : d) :
    finiteProjectiveCharacterDetuning
        (pairProjectiveCharacter i j) omega =
      omega i - omega j := by
  classical
  rw [finiteProjectiveCharacterDetuning]
  simp only [pairProjectiveCharacter]
  rw [Finsupp.sum_sub_index (by
    intro a b₁ b₂
    push_cast
    ring)]
  simp

/-- Weighted quadratic projective-phase statistic.  With probability
weights, this is the survival fidelity, equivalently the finite spectral
form factor normalized by total weight. -/
def finiteWeightedReturnPolynomial
    {d : Type*} [Fintype d]
    (weight : d → ℝ) :
    C(UnitAddTorus d, ℂ) :=
  projectiveCharacterPolynomial
    (fun p : d × d =>
      ((weight p.1 * weight p.2 : ℝ) : ℂ))
    (fun p => pairProjectiveCharacter p.1 p.2)

/-- Exact finite-window recurrence projection: the expected weighted
return polynomial is the gap-weighted sinc sum. -/
theorem integral_finiteWeightedReturnPolynomial_phaseMeasure
    {d : Type*} [Fintype d]
    (weight omega : d → ℝ) (clock : ℝ) :
    (∫ x, finiteWeightedReturnPolynomial weight x
        ∂(finiteTorusPhaseProbabilityMeasure omega clock :
          Measure (UnitAddTorus d))) =
      ∑ p : d × d,
        ((weight p.1 * weight p.2 : ℝ) : ℂ) *
          Real.sinc
            (clock * (omega p.1 - omega p.2)) := by
  rw [finiteWeightedReturnPolynomial,
    integral_projectiveCharacterPolynomial]
  apply Finset.sum_congr rfl
  intro p hp
  rw [projectivePhaseLawFourierCoefficient,
    finiteTorusPhaseProbabilityMeasure_mFourier_integral,
    finiteTorusCharacterDetuning_finiteCharacterOfProjective,
    finiteProjectiveCharacterDetuning_pair]

/-- Every observer-action limit law fixes the weighted recurrence
statistic by evaluating the same action profile on ordered-pair
characters. -/
theorem integral_finiteWeightedReturnPolynomial_actionProfile
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (profile : (d → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profile n))
    (weight : d → ℝ) :
    (∫ x, finiteWeightedReturnPolynomial weight x
        ∂(μ : Measure (UnitAddTorus d))) =
      ∑ p : d × d,
        ((weight p.1 * weight p.2 : ℝ) : ℂ) *
          observerActionRegimeCoefficient
            (profile
              (finiteCharacterOfProjective
                (pairProjectiveCharacter p.1 p.2))) := by
  rw [finiteWeightedReturnPolynomial,
    integral_projectiveCharacterPolynomial]
  apply Finset.sum_congr rfl
  intro p hp
  rw [projectivePhaseLawFourierCoefficient,
    hcoeff]

/-- **Recurrence projection law.** Weak convergence of the complete phase
history forces convergence of every finite weighted return statistic to
the value selected by the observer-action profile. -/
theorem finiteWeightedReturn_tendsto_actionProfile
    {α d : Type*} [Fintype d]
    {l : Filter α}
    (omega : α → d → ℝ) (clock : α → ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun x =>
          finiteTorusPhaseProbabilityMeasure
            (omega x) (clock x))
        l (𝓝 μ))
    (profile : (d → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profile n))
    (weight : d → ℝ) :
    Tendsto
      (fun x =>
        ∫ y, finiteWeightedReturnPolynomial weight y
          ∂(finiteTorusPhaseProbabilityMeasure
            (omega x) (clock x) :
              Measure (UnitAddTorus d)))
      l
      (𝓝
        (∑ p : d × d,
          ((weight p.1 * weight p.2 : ℝ) : ℂ) *
            observerActionRegimeCoefficient
              (profile
                (finiteCharacterOfProjective
                  (pairProjectiveCharacter p.1 p.2))))) := by
  have h :=
    (continuous_integral_complex_continuousMap
      (finiteWeightedReturnPolynomial weight)).continuousAt.tendsto.comp hμ
  rw [integral_finiteWeightedReturnPolynomial_actionProfile
    μ profile hcoeff weight] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
