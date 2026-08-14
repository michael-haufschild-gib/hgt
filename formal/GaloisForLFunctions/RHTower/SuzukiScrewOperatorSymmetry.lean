import GaloisForLFunctions.RHTower.SuzukiScrewOperatorAction

/-!
# Formal self-adjointness of Suzuki's natural product

The exact maximal-adjoint witness identifies the action of `D† Gₐ D` on its natural domain.
The inverse-primitive pairing and self-adjointness of the compressed screw operator `Gₐ` then
prove that this literal product is formally self-adjoint on its established domain
`H₀¹(-a,a)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- Pairing a zero-mean primitive against the maximal-adjoint screw witness recovers the
compressed screw form exactly. -/
theorem inner_suzukiDirichletInverse_rawScrewAdjointWitness
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureZeroMean a) :
    inner ℂ (suzukiDirichletInverseCLM a f)
        (suzukiRawScrewAdjointWitness a
          (g : SuzukiApertureIntervalL2 a.1)) =
      inner ℂ f (suzukiScrewZeroMeanOperator a g) := by
  rw [inner_suzukiDirichletInverse_eq_adjoint,
    suzukiDirichletInverseAdjointCLM_adjointWitness_eq]

/-- Suzuki's literal natural product `D† Gₐ D` is formally self-adjoint on its proved
`H₀¹(-a,a)` domain. -/
theorem suzukiDirichletScrewOperator_isFormalAdjoint
    (a : SuzukiPositiveAperture) :
    (suzukiDirichletScrewOperator a).IsFormalAdjoint
      (suzukiDirichletScrewOperator a) := by
  intro v w
  let vd : (suzukiDirichletDerivative a).domain :=
    ⟨v.1, by
      rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
      exact v.property⟩
  let wd : (suzukiDirichletDerivative a).domain :=
    ⟨w.1, by
      rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
      exact w.property⟩
  let f : SuzukiApertureZeroMean a :=
    (suzukiDirichletInverseRangeEquiv a).symm
      (suzukiDirichletDomainToH01 a vd)
  let g : SuzukiApertureZeroMean a :=
    (suzukiDirichletInverseRangeEquiv a).symm
      (suzukiDirichletDomainToH01 a wd)
  have hv : (v : SuzukiApertureIntervalL2 a.1) =
      suzukiDirichletInverseCLM a f := by
    change v.1 = suzukiAperturePrimitive a.1
      (f : SuzukiApertureIntervalL2 a.1)
    symm
    exact suzukiAperturePrimitive_dirichletDomainDerivativeCoordinate a vd
  have hw : (w : SuzukiApertureIntervalL2 a.1) =
      suzukiDirichletInverseCLM a g := by
    change w.1 = suzukiAperturePrimitive a.1
      (g : SuzukiApertureIntervalL2 a.1)
    symm
    exact suzukiAperturePrimitive_dirichletDomainDerivativeCoordinate a wd
  have hf : (f : SuzukiApertureIntervalL2 a.1) =
      suzukiDirichletDomainDerivativeCoordinate a vd := rfl
  have hg : (g : SuzukiApertureIntervalL2 a.1) =
      suzukiDirichletDomainDerivativeCoordinate a wd := rfl
  have hG := (suzukiScrewZeroMeanOperator_isSelfAdjoint a).isSymmetric f g
  rw [suzukiDirichletScrewOperator_apply_eq_adjointWitness,
    suzukiDirichletScrewOperator_apply_eq_adjointWitness]
  rw [show (⟨v.1, by
      rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
      exact v.property⟩ : (suzukiDirichletDerivative a).domain) = vd from rfl,
    show (⟨w.1, by
      rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
      exact w.property⟩ : (suzukiDirichletDerivative a).domain) = wd from rfl,
    ← hf, ← hg, hv, hw]
  calc
    inner ℂ (suzukiRawScrewAdjointWitness a
        (f : SuzukiApertureIntervalL2 a.1))
        (suzukiDirichletInverseCLM a g) =
        (starRingEnd ℂ) (inner ℂ (suzukiDirichletInverseCLM a g)
          (suzukiRawScrewAdjointWitness a
            (f : SuzukiApertureIntervalL2 a.1))) :=
      (inner_conj_symm (𝕜 := ℂ) _ _).symm
    _ = (starRingEnd ℂ) (inner ℂ g (suzukiScrewZeroMeanOperator a f)) := by
      rw [inner_suzukiDirichletInverse_rawScrewAdjointWitness]
    _ = inner ℂ (suzukiScrewZeroMeanOperator a f) g :=
      inner_conj_symm (𝕜 := ℂ)
        (suzukiScrewZeroMeanOperator a f : SuzukiApertureZeroMean a) g
    _ = inner ℂ f (suzukiScrewZeroMeanOperator a g) := hG
    _ = inner ℂ (suzukiDirichletInverseCLM a f)
        (suzukiRawScrewAdjointWitness a
          (g : SuzukiApertureIntervalL2 a.1)) :=
      (inner_suzukiDirichletInverse_rawScrewAdjointWitness a f g).symm

end RHTower

end
