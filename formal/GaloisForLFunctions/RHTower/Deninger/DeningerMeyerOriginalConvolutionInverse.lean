import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionInverseSource
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionTopology

/-! # Continuous convolution solving in the original Meyer quotient

The spectral repair and its inverse act in the original all-weight quotient
topology. The Hilbert completion supplies no additional source-admission
premise: the inverse correction is an actual convolution kernel.
-/

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

local notation "V" => DeningerMeyerStrongLogTarget
local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "H" => deningerMeyerHasseHilbertLM
local notation "C" => deningerMeyerCohomologyConvolution

theorem deningerMeyerCohomologyConvolution_continuous (g : V) :
    Continuous (C (Submodule.Quotient.mk g)) := by
  apply (LinearMap.range deningerMeyerStrongLogSumLM).isQuotientMap_mkQ.continuous_iff.mpr
  exact continuous_quot_mk.comp (deningerMeyerSourceConvolution_continuous g)

def deningerMeyerOriginalConvolutionRepair (g : V) : Module.End ℂ Q :=
  LinearMap.id + (C (Submodule.Quotient.mk g)).comp
    (LinearMap.id-deningerMeyerFiniteXiCausalProjector (deningerMeyerConvolutionResonantPacket g))

def deningerMeyerOriginalConvolutionInverse (g : V) : Module.End ℂ Q :=
  LinearMap.id+C (Submodule.Quotient.mk (deningerMeyerConvolutionInverseKernel g))

theorem deningerMeyerOriginalConvolutionRepair_hilbert (g : V) (u : Q) :
    H (deningerMeyerOriginalConvolutionRepair g u) =
      deningerMeyerConvolutionFredholmRepair g (H u) :=
  (deningerMeyerConvolutionRepair_source g u).symm

theorem deningerMeyerOriginalConvolutionInverse_hilbert (g : V) (u : Q) :
    H (deningerMeyerOriginalConvolutionInverse g u) =
      deningerMeyerConvolutionFredholmInverse g (H u) :=
  (deningerMeyerConvolutionFredholmInverse_source g u).symm

theorem deningerMeyerOriginalConvolutionInverse_left (g : V) (u : Q) :
    deningerMeyerOriginalConvolutionInverse g (deningerMeyerOriginalConvolutionRepair g u) = u := by
  apply deningerMeyerHasseHilbertLM_injective
  rw [deningerMeyerOriginalConvolutionInverse_hilbert,
    deningerMeyerOriginalConvolutionRepair_hilbert, deningerMeyerConvolutionFredholmInverse_left]

theorem deningerMeyerOriginalConvolutionInverse_right (g : V) (u : Q) :
    deningerMeyerOriginalConvolutionRepair g (deningerMeyerOriginalConvolutionInverse g u) = u := by
  apply deningerMeyerHasseHilbertLM_injective
  rw [deningerMeyerOriginalConvolutionRepair_hilbert,
    deningerMeyerOriginalConvolutionInverse_hilbert, deningerMeyerConvolutionFredholmInverse_right]

theorem deningerMeyerOriginalConvolutionRepair_continuous (g : V) :
    Continuous (deningerMeyerOriginalConvolutionRepair g) :=
  continuous_id.add ((deningerMeyerCohomologyConvolution_continuous g).comp
    (continuous_id.sub ((deningerMeyerFiniteXiCausalSection_continuous _).comp
      (deningerMeyerFiniteXiJetPacketLM_continuous _))))

theorem deningerMeyerOriginalConvolutionInverse_continuous (g : V) :
    Continuous (deningerMeyerOriginalConvolutionInverse g) :=
  continuous_id.add (deningerMeyerCohomologyConvolution_continuous
    (deningerMeyerConvolutionInverseKernel g))

/-- Every repaired original convolution equation has a continuous original
inverse, with the same full-multiplicity resonance repair as on Hilbert space. -/
def deningerMeyerOriginalConvolutionContinuousEquiv (g : V) : Q ≃L[ℂ] Q where
  toLinearEquiv :=
    { toLinearMap := deningerMeyerOriginalConvolutionRepair g
      invFun := deningerMeyerOriginalConvolutionInverse g
      left_inv := deningerMeyerOriginalConvolutionInverse_left g
      right_inv := deningerMeyerOriginalConvolutionInverse_right g }
  continuous_toFun := deningerMeyerOriginalConvolutionRepair_continuous g
  continuous_invFun := deningerMeyerOriginalConvolutionInverse_continuous g

theorem deningerMeyerOriginalConvolutionRepair_existsUnique (g : V) (f : Q) :
    ∃! x : Q, deningerMeyerOriginalConvolutionRepair g x = f := by
  refine ⟨deningerMeyerOriginalConvolutionInverse g f,
    deningerMeyerOriginalConvolutionInverse_right g f, fun x hx => ?_⟩
  rw [← deningerMeyerOriginalConvolutionInverse_left g x, hx]

/-- The exact finite compatibility reduction now holds on literal original
cohomology, with an admitted continuous solution on the complement. -/
theorem deningerMeyerOriginalConvolution_equation_iff (g : V) (f x : Q) :
    let P := deningerMeyerFiniteXiCausalProjector (deningerMeyerConvolutionResonantPacket g)
    x+C (Submodule.Quotient.mk g) x = f ↔
      P x+C (Submodule.Quotient.mk g) (P x) = P f ∧
      x-P x = deningerMeyerOriginalConvolutionInverse g (f-P f) := by
  dsimp only
  have he : x+C (Submodule.Quotient.mk g) x = f ↔
      H x+deningerMeyerHilbertConvolution g (H x) = H f := by
    rw [← deningerMeyerHasseHilbertLM_injective.eq_iff, map_add,
      ← deningerMeyerHilbertConvolution_source]
  rw [he, deningerMeyerConvolution_equation_iff]
  simp only [deningerMeyerConvolution_projection_source,
    deningerMeyerHilbertConvolution_source, ← map_add, ← map_sub,
    ← deningerMeyerOriginalConvolutionInverse_hilbert,
    deningerMeyerHasseHilbertLM_injective.eq_iff]

end
end RHTower
