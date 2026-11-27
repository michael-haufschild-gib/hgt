import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGlobalLineBundleSections
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! The degree-zero Čech cohomology is the module of global sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.LineBundleSections

/-- For a cover of the whole scheme, the degree-zero cocycles correspond to
global sections, and the incoming differential vanishes. -/
def cechHomologyZeroEquiv {R : Type} [CommRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of R)) (F : X.Modules) {ι : Type} [LinearOrder ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    letI := sectionBaseModule f F ⊤
    (cech f F U).homology 0 ≃ₗ[R] Γ(F, ⊤) := by
  letI := sectionBaseModule f F ⊤
  let C := cech f F U
  let cyclesIso : C.cycles 0 ≅ kernel (C.d 0 1) :=
    (C.cyclesIsKernel 0 1 (by simp)).conePointUniqueUpToIso (limit.isLimit _)
  let e : C.homology 0 ≅ ModuleCat.of R (LinearMap.ker (C.d 0 1).hom) :=
    C.isoHomologyπ₀.symm ≪≫ cyclesIso ≪≫ ModuleCat.kernelIsoKer (C.d 0 1)
  exact e.toLinearEquiv.trans (globalSectionsLinearEquivKernel f F U hU.ge).symm

end GlobalTheory.LineBundleSections
