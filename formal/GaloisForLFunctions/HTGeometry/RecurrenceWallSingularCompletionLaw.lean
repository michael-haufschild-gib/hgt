import GaloisForLFunctions.HTGeometry.UniversalProjectiveRecurrencePhaseDiagramLaw
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Singular completion at recurrence walls

Every nonzero finite-time recurrence reporter is continuous in control
space.  Its completed-time limit is the exact wall indicator, which is
discontinuous at every transverse wall point.  Together with the exact sinc
normal profile, this identifies recurrence-wall crossing as a singular
infinite-time limit rather than a finite-time discontinuity.
-/

open Filter Set Topology
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Completed-time order parameter of one controlled recurrence character. -/
def completedControlledRecurrenceWallIndicator
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x : X) : ℂ :=
  by
    classical
    exact if x ∈ projectiveControlRecurrenceWall energy response k then 1 else 0

/-- Every controlled wall reporter converges pointwise to the exact wall indicator. -/
theorem controlledRecurrenceWallReporter_tendsto_completedIndicator
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x : X) :
    Tendsto (fun T => controlledRecurrenceWallReporter k energy response T x)
      atTop (𝓝 (completedControlledRecurrenceWallIndicator k energy response x)) := by
  classical
  by_cases hzero : projectiveCharacterDetuning k
      (controlledProjectiveEnergy energy response x) = 0
  · have hwall : x ∈ projectiveControlRecurrenceWall energy response k := hzero
    simpa [controlledRecurrenceWallReporter,
      completedControlledRecurrenceWallIndicator, hwall, hzero] using
        symmetricPhaseAverage_tendsto_resonanceIndicator
          (projectiveCharacterDetuning k
            (controlledProjectiveEnergy energy response x))
  · have hwall : x ∉ projectiveControlRecurrenceWall energy response k := hzero
    simpa [controlledRecurrenceWallReporter,
      completedControlledRecurrenceWallIndicator, hwall, hzero] using
        symmetricPhaseAverage_tendsto_resonanceIndicator
          (projectiveCharacterDetuning k
            (controlledProjectiveEnergy energy response x))

/-- At every nonzero observation time, the wall reporter is continuous in all controls. -/
theorem continuous_controlledRecurrenceWallReporter
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (T : ℝ) (hT : T ≠ 0) :
    Continuous (fun x => controlledRecurrenceWallReporter k energy response T x) := by
  have heq :
      (fun x => controlledRecurrenceWallReporter k energy response T x) =
        (fun x => (Real.sinc
          (T * (projectiveCharacterDetuning k energy +
            projectiveControlDetuning k response x)) : ℂ)) := by
    funext x
    rw [controlledRecurrenceWallReporter,
      symmetricPhaseAverage_eq_sinc _ _ hT,
      projectiveCharacterDetuning_controlledEnergy]
  rw [heq]
  fun_prop

/-- The completed wall indicator is discontinuous at every transverse wall point. -/
theorem not_continuousAt_completedControlledRecurrenceWallIndicator
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x₀ : X)
    (hwall : x₀ ∈ projectiveControlRecurrenceWall energy response k)
    (htransverse : projectiveControlDetuning k response ≠ 0) :
    ¬ ContinuousAt
      (completedControlledRecurrenceWallIndicator k energy response) x₀ := by
  intro hcontinuous
  obtain ⟨v, hv⟩ : ∃ v : X, projectiveControlDetuning k response v ≠ 0 := by
    simpa [ContinuousLinearMap.ext_iff] using htransverse
  let y : ℕ → X := fun n =>
    x₀ + (1 / ((n : ℝ) + 1)) • v
  have hy : Tendsto y atTop (𝓝 x₀) := by
    have hcoeff :
        Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [y] using
      (tendsto_const_nhds.add (hcoeff.smul_const v) :
        Tendsto (fun n : ℕ => x₀ + (1 / ((n : ℝ) + 1)) • v)
          atTop (𝓝 (x₀ + (0 : ℝ) • v)))
  have hyoff : ∀ n, y n ∉ projectiveControlRecurrenceWall energy response k := by
    intro n hyn
    rw [mem_projectiveControlRecurrenceWall_iff] at hwall hyn
    have hcoef : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
    have hprod : (1 / ((n : ℝ) + 1)) *
        projectiveControlDetuning k response v = 0 := by
      dsimp [y] at hyn
      rw [map_add, map_smul] at hyn
      simpa only [smul_eq_mul, hwall, add_eq_left] using hyn
    exact hv ((mul_eq_zero.mp hprod).resolve_left hcoef)
  have htoOne :
      Tendsto
        (fun n => completedControlledRecurrenceWallIndicator k energy response (y n))
        atTop (𝓝 (1 : ℂ)) := by
    have hx₀ : completedControlledRecurrenceWallIndicator k energy response x₀ = 1 := by
      simp [completedControlledRecurrenceWallIndicator, hwall]
    have h := hcontinuous.tendsto.comp hy
    rw [hx₀] at h
    change Tendsto
      (completedControlledRecurrenceWallIndicator k energy response ∘ y)
      atTop (𝓝 (1 : ℂ))
    exact h
  have htoZero :
      Tendsto
        (fun n => completedControlledRecurrenceWallIndicator k energy response (y n))
        atTop (𝓝 (0 : ℂ)) := by
    have heq :
        (fun n => completedControlledRecurrenceWallIndicator k energy response (y n)) =
          (fun _ : ℕ => (0 : ℂ)) := by
      funext n
      simp [completedControlledRecurrenceWallIndicator, hyoff n]
    rw [heq]
    exact tendsto_const_nhds
  have : (1 : ℂ) = 0 := tendsto_nhds_unique htoOne htoZero
  exact one_ne_zero this

/-- **Singular recurrence-completion law.** Finite-time continuity and completed-time
wall singularity hold simultaneously for every transverse character wall. -/
theorem recurrenceWall_singularCompletionLaw
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x₀ : X)
    (hwall : x₀ ∈ projectiveControlRecurrenceWall energy response k)
    (htransverse : projectiveControlDetuning k response ≠ 0) :
    (∀ T : ℝ, T ≠ 0 →
      Continuous (fun x => controlledRecurrenceWallReporter k energy response T x)) ∧
    (∀ x : X,
      Tendsto (fun T => controlledRecurrenceWallReporter k energy response T x)
        atTop (𝓝 (completedControlledRecurrenceWallIndicator k energy response x))) ∧
    ¬ ContinuousAt
      (completedControlledRecurrenceWallIndicator k energy response) x₀ := by
  exact ⟨continuous_controlledRecurrenceWallReporter k energy response,
    controlledRecurrenceWallReporter_tendsto_completedIndicator k energy response,
    not_continuousAt_completedControlledRecurrenceWallIndicator
      k energy response x₀ hwall htransverse⟩

end
end GaloisForLFunctions.HTGeometry
