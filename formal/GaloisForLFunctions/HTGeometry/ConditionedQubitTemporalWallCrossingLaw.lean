import GaloisForLFunctions.HTGeometry.ConditionedQubitSpectralBirthProfiles
import GaloisForLFunctions.HTGeometry.SymmetricTimeAverageWallCrossingLaw

/-!
# Two temporal wall crossings of conditioned-qubit spectral characters

The exact birth profiles of the conditioned-qubit spectrum instantiate the
universal symmetric-window wall-crossing law at orders one and two.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Exact positive birth profile of the first spectral character. -/
theorem conditionedQubitLayerOne_hasPositiveBirthProfile :
    HasPositiveBirthProfile conditionedQubitLayerOneDetuning 1 2 := by
  constructor
  · simpa [pow_one] using conditionedQubitLayerOne_profile
  · norm_num

/-- Exact positive birth profile of the second spectral character. -/
theorem conditionedQubitLayerTwo_hasPositiveBirthProfile :
    HasPositiveBirthProfile conditionedQubitLayerTwoDetuning 2 3 := by
  exact ⟨conditionedQubitLayerTwo_profile, by norm_num⟩

/-- Actual symmetric-window wall crossing of the first spectral character
on its `g⁻¹` horizon. -/
theorem conditionedQubitLayerOne_symmetricPhaseAverage_wallCrossing
    {τ : ℝ} (hτ : 0 < τ) :
    (∀ r < 1,
      Tendsto
        (fun g =>
          symmetricPhaseAverage
            (τ / g ^ r) (conditionedQubitLayerOneDetuning g))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g =>
        symmetricPhaseAverage
          (τ / g) (conditionedQubitLayerOneDetuning g))
      (𝓝[>] 0) (𝓝 (Real.sinc (τ * 2))) ∧
    (∀ r, 1 < r →
      Tendsto
        (fun g =>
          symmetricPhaseAverage
            (τ / g ^ r) (conditionedQubitLayerOneDetuning g))
        (𝓝[>] 0) (𝓝 0)) := by
  simpa [pow_one] using
    symmetricPhaseAverage_wallCrossing
      conditionedQubitLayerOne_hasPositiveBirthProfile hτ

/-- Actual symmetric-window wall crossing of the second spectral character
on its `g⁻²` horizon. -/
theorem conditionedQubitLayerTwo_symmetricPhaseAverage_wallCrossing
    {τ : ℝ} (hτ : 0 < τ) :
    (∀ r < 2,
      Tendsto
        (fun g =>
          symmetricPhaseAverage
            (τ / g ^ r) (conditionedQubitLayerTwoDetuning g))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g =>
        symmetricPhaseAverage
          (τ / g ^ (2 : ℕ)) (conditionedQubitLayerTwoDetuning g))
      (𝓝[>] 0) (𝓝 (Real.sinc (τ * 3))) ∧
    (∀ r, 2 < r →
      Tendsto
        (fun g =>
          symmetricPhaseAverage
            (τ / g ^ r) (conditionedQubitLayerTwoDetuning g))
        (𝓝[>] 0) (𝓝 0)) :=
  symmetricPhaseAverage_wallCrossing
    conditionedQubitLayerTwo_hasPositiveBirthProfile hτ

end GaloisForLFunctions.HTGeometry
