import GaloisForLFunctions.HilbertMetric.FiniteOrbitFrames
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel

/-!
# Observation quotients of finite frames

Observations modulo those factoring through the frame operator are precisely
observations on the orthogonal complement of the frame span. This applies the
operator-quotient mechanism of Zehavi, Proposition 3.29, arXiv:2611.18218,
to finite frames and complete unitary group orbits.
-/

noncomputable section

open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RepresentationLifting.OperatorKernels

namespace HilbertMetric

variable {ι E W : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [AddCommGroup W] [Module ℂ W]

/-- A linear observation factors through a frame exactly when it kills every invisible vector. -/
theorem finiteFrame_observation_factors_iff (v : ι → E) (f : E →ₗ[ℂ] W) :
    (∃ g : E →ₗ[ℂ] W, g.comp (frameOperator v).toLinearMap = f) ↔
      ∀ x, (∀ i, inner ℂ (v i) x = 0) → f x = 0 := by
  change f ∈ (precompose (frameOperator v).toLinearMap).range ↔ _
  rw [range_precompose]
  constructor
  · intro h x hx
    exact LinearMap.congr_fun h ⟨x, (finite_frame_eq_zero_iff v x).mpr hx⟩
  · intro h
    apply LinearMap.ext
    intro x
    exact h x.val ((finite_frame_eq_zero_iff v x.val).mp x.property)

/-- Each direction orthogonal to the frame span contributes a full observation space. -/
theorem finiteFrame_observation_defect [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    (v : ι → E) :
    Module.finrank ℂ ((E →ₗ[ℂ] W) ⧸
      (precompose (W := W) (frameOperator v).toLinearMap).range) =
      Module.finrank ℂ W * Module.finrank ℂ (Submodule.span ℂ (Set.range v))ᗮ := by
  rw [finrank_compositionCokernel]
  congr 1
  exact congrArg (fun S : Submodule ℂ E => Module.finrank ℂ S) (finite_frame_ker v)

/-- The full endomorphism quotient measures undetected dimensions with ambient multiplicity. -/
theorem finiteFrame_endomorphism_defect [FiniteDimensional ℂ E] (v : ι → E) :
    Module.finrank ℂ (Module.End ℂ E ⧸
      (precompose (W := E) (frameOperator v).toLinearMap).range) =
      Module.finrank ℂ E * Module.finrank ℂ (Submodule.span ℂ (Set.range v))ᗮ :=
  finiteFrame_observation_defect v

/-- Orbit symmetry leaves exactly the observations on the orthogonal cyclic sector. -/
theorem orbitFrame_observation_defect [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    {G : Type*} [Group G] [Fintype G] (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (e : E) :
    Module.finrank ℂ ((E →ₗ[ℂ] W) ⧸
      (precompose (W := W) (orbitFrame ρ e).toLinearMap).range) =
      Module.finrank ℂ W *
        Module.finrank ℂ (Submodule.span ℂ (Set.range fun g => ρ g e))ᗮ :=
  finiteFrame_observation_defect (fun g => ρ g e)

end HilbertMetric

#print axioms HilbertMetric.finiteFrame_observation_factors_iff
#print axioms HilbertMetric.finiteFrame_observation_defect
#print axioms HilbertMetric.orbitFrame_observation_defect
