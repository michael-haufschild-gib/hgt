import GaloisForLFunctions.HTGeometry.ChronometricCausalSusceptibility
import GaloisForLFunctions.HTGeometry.ClockResponseIdentifiability

/-!
# Conservation-constrained drives determine the response

A laboratory cannot prescribe an arbitrary clock source: the source must carry the adaptive
component that cancels the conservation defect. The question is whether that constraint removes
drives the reconstruction needs.

It does not. When the clock gradients form a coframe, the conservation-balanced sources exhaust the
whole source space — every source is balanced, for exactly one defect — so the constrained drive
family has the same span as the unconstrained one, and identifiability is untouched.
-/

namespace GaloisForLFunctions.HTGeometry

section Exhaustive

variable {R Curv Clock : Type*} [Ring R] [AddCommGroup Curv] [Module R Curv]
  [AddCommGroup Clock] [Module R Clock]

/-- **Every clock source is conservation-balanced.** Given the source, the defect it cancels is
determined, so the balancing construction loses no source channel. -/
theorem conservationBalancedClockSourceWithSignal_surjective (clockCoframe : Clock ≃ₗ[R] Curv)
    {Signal : Type*} :
    Function.Surjective
      (fun data : Curv × Signal =>
        conservationBalancedClockSourceWithSignal clockCoframe data.1 data.2) := by
  rintro ⟨a, s⟩
  refine ⟨(-clockCoframe a, s), ?_⟩
  simp [conservationBalancedClockSourceWithSignal, conservationBalancedClockSource]

/-- The conservation-balanced sources are exactly the sources, in bijection with defect and
signal. -/
theorem conservationBalancedClockSourceWithSignal_bijective (clockCoframe : Clock ≃ₗ[R] Curv)
    {Signal : Type*} :
    Function.Bijective
      (fun data : Curv × Signal =>
        conservationBalancedClockSourceWithSignal clockCoframe data.1 data.2) :=
  ⟨conservationBalancedClockSourceWithSignal_injective clockCoframe,
    conservationBalancedClockSourceWithSignal_surjective clockCoframe⟩

end Exhaustive

section Drives

variable {𝕜 : Type*} [RCLike 𝕜]
variable {Clock Curv Signal F : Type*}
  [NormedAddCommGroup Clock] [NormedSpace 𝕜 Clock]
  [AddCommGroup Curv] [Module 𝕜 Curv]
  [NormedAddCommGroup Signal] [NormedSpace 𝕜 Signal]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ι : Type*}

/-- **Conservation constraints do not shrink the drive family.** Two response operators whose
readings agree on every conservation-balanced source are equal: the constrained drives already span
the whole source space. -/
theorem responseOperator_eq_of_conservationBalanced_data (clockCoframe : Clock ≃ₗ[𝕜] Curv)
    {T S : (Clock × Signal) →L[𝕜] F} {readout : ι → F →L[𝕜] 𝕜}
    (hread : SeparatingReadouts readout)
    (hdata : ∀ (i : ι) (defect : Curv) (signal : Signal),
      readout i (T (conservationBalancedClockSourceWithSignal clockCoframe defect signal)) =
        readout i (S (conservationBalancedClockSourceWithSignal clockCoframe defect signal))) :
    T = S := by
  have hrange : Set.range
      (fun data : Curv × Signal =>
        conservationBalancedClockSourceWithSignal clockCoframe data.1 data.2) = Set.univ :=
    Set.range_eq_univ.mpr (conservationBalancedClockSourceWithSignal_surjective clockCoframe)
  have hdense : Dense (Submodule.span 𝕜
      (Set.range fun data : Curv × Signal =>
        conservationBalancedClockSourceWithSignal clockCoframe data.1 data.2) :
      Set (Clock × Signal)) := by
    rw [hrange, Submodule.span_univ]
    simp
  exact responseOperator_eq_of_data hdense hread fun i j => hdata i j.1 j.2

end Drives

end GaloisForLFunctions.HTGeometry
