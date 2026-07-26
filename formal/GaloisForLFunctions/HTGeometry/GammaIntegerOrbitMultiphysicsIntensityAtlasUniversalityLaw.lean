import GaloisForLFunctions.HTGeometry.GammaIntegerOrbitMultiphysicsPhaseAtlasUniversalityLaw
import GaloisForLFunctions.HTGeometry.GammaReflectedIntensityExactCollapseUniversalityLaw
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Integer-orbit multiphysics/intensity atlas universality

On the symmetric reflected-frequency slice, the relative Gamma-weight difference and both
absolute thermal weights reduce to the same affine selector up to sign.  The exact reflected-
intensity collapse locus therefore joins the existing twelve-observable Gamma phase atlas without
introducing a new exceptional branch.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- On the symmetric reflected-frequency slice, intensity collapses exactly on the integer orbit
of the shared selector. -/
theorem differentialAlgebraicOver_gammaOppositeShiftIntensityMero_symmetricSlice_iff_integer
    (delta : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaOppositeShiftIntensityMero ((1 - delta) / 2) ((1 + delta) / 2)) ↔
      ∃ k : ℤ, delta = (k : ℂ) := by
  rw [differentialAlgebraicOver_gammaOppositeShiftIntensityMero_iff_exactCollapse]
  constructor
  · rintro (⟨k, hk⟩ | ⟨⟨k, hk⟩, _⟩)
    · refine ⟨k, ?_⟩
      linear_combination hk
    · refine ⟨k, ?_⟩
      linear_combination hk
  · rintro ⟨k, hk⟩
    left
    refine ⟨k, ?_⟩
    linear_combination hk

/-- Off the shared integer orbit, symmetric reflected intensity is exactly HT. -/
theorem hypertranscendentalOver_gammaOppositeShiftIntensityMero_symmetricSlice_iff_noninteger
    (delta : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (gammaOppositeShiftIntensityMero ((1 - delta) / 2) ((1 + delta) / 2)) ↔
      ∀ k : ℤ, delta ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_gammaOppositeShiftIntensityMero_symmetricSlice_iff_integer]
  push Not
  rfl

/-- Simultaneous DA phase for the twelve-observable atlas and symmetric reflected intensity. -/
structure GammaIntegerOrbitMultiphysicsIntensityCollapseCertificate
    (a delta lambda : ℂ) : Prop where
  multiphysics : GammaIntegerOrbitMultiphysicsCollapseCertificate a delta lambda
  reflectedIntensity : DifferentialAlgebraicOver (RatFunc ℂ)
    (gammaOppositeShiftIntensityMero ((1 - delta) / 2) ((1 + delta) / 2))

/-- Simultaneous HT phase for the same thirteen observables. -/
structure GammaIntegerOrbitMultiphysicsIntensityNoncollapseCertificate
    (a delta lambda : ℂ) : Prop where
  multiphysics : GammaIntegerOrbitMultiphysicsNoncollapseCertificate a delta lambda
  reflectedIntensity : HypertranscendentalOver (RatFunc ℂ)
    (gammaOppositeShiftIntensityMero ((1 - delta) / 2) ((1 + delta) / 2))

/-- **Thirteen-observable collapse law.**  The existing multiphysics atlas and symmetric
reflected intensity collapse together exactly on one integer orbit. -/
theorem gammaIntegerOrbit_multiphysicsIntensity_simultaneousCollapse
    (a delta lambda : ℂ) :
    (∃ k : ℤ, delta = (k : ℂ)) ↔
      GammaIntegerOrbitMultiphysicsIntensityCollapseCertificate a delta lambda := by
  constructor
  · intro hdelta
    exact ⟨(gammaIntegerOrbit_multiphysics_simultaneousCollapse
      a delta lambda).1 hdelta,
      (differentialAlgebraicOver_gammaOppositeShiftIntensityMero_symmetricSlice_iff_integer
        delta).2 hdelta⟩
  · intro h
    exact (gammaIntegerOrbit_multiphysics_simultaneousCollapse
      a delta lambda).2 h.multiphysics

/-- **Thirteen-observable noncollapse law.**  All thirteen observables are HT exactly off the
same integer orbit. -/
theorem gammaIntegerOrbit_multiphysicsIntensity_simultaneousHypertranscendence
    (a delta lambda : ℂ) :
    (∀ k : ℤ, delta ≠ (k : ℂ)) ↔
      GammaIntegerOrbitMultiphysicsIntensityNoncollapseCertificate a delta lambda := by
  constructor
  · intro hdelta
    exact ⟨(gammaIntegerOrbit_multiphysics_simultaneousHypertranscendence
      a delta lambda).1 hdelta,
      (hypertranscendentalOver_gammaOppositeShiftIntensityMero_symmetricSlice_iff_noninteger
        delta).2 hdelta⟩
  · intro h
    exact (gammaIntegerOrbit_multiphysics_simultaneousHypertranscendence
      a delta lambda).2 h.multiphysics

/-- The thirteen-observable DA and HT phases are exact complements. -/
theorem gammaIntegerOrbit_multiphysicsIntensity_phaseComplement
    (a delta lambda : ℂ) :
    (¬ GammaIntegerOrbitMultiphysicsIntensityCollapseCertificate a delta lambda) ↔
      GammaIntegerOrbitMultiphysicsIntensityNoncollapseCertificate a delta lambda := by
  constructor
  · intro hnot
    apply (gammaIntegerOrbit_multiphysicsIntensity_simultaneousHypertranscendence
      a delta lambda).1
    intro k hk
    apply hnot
    exact (gammaIntegerOrbit_multiphysicsIntensity_simultaneousCollapse
      a delta lambda).1 ⟨k, hk⟩
  · intro hnoncollapse hcollapse
    have hinteger := (gammaIntegerOrbit_multiphysicsIntensity_simultaneousCollapse
      a delta lambda).2 hcollapse
    have hnoninteger := (gammaIntegerOrbit_multiphysicsIntensity_simultaneousHypertranscendence
      a delta lambda).2 hnoncollapse
    obtain ⟨k, hk⟩ := hinteger
    exact hnoninteger k hk

end

end GaloisForLFunctions
