import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechHomologyComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineQuasicoherentAcyclic

/-! Vanishing of first sheaf cohomology makes the affine Čech complex exact in degree one. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

theorem cech_exact_of_H1_zero
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (F : X.Modules) [F.IsQuasicoherent] {ι : Type} [DecidableEq ι] [LinearOrder ι]
    (U : ι → X.Opens) (hc : ⊤ ≤ ⨆ i, U i)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (coverInter ⊤ U s))
    (h : Subsingleton (CohomologyOn F ⊤ 1)) :
    Function.Exact ((cech f F U).d 0 1).hom ((cech f F U).d 1 2).hom := by
  let C := cech f F U
  let e := cechCohomologyEquiv f F U 1
  have a : ModuleCechCohomology ⊤ U F 1 ≃ₗ[Γ(X, ⊤)] CohomologyOn F ⊤ 1 := by
    have b := moduleLerayLinearEquiv ⊤ U F 1 hc
      (fun s hs => quasicoherent_acyclicOn F (hU s hs))
    rwa [coverInter_empty] at b
  haveI : Subsingleton (C.homology 1) :=
    ⟨fun x y => (a.injective.comp e.injective) (h.elim _ _)⟩
  have he : C.ExactAt 1 := (C.exactAt_iff_isZero_homology 1).mpr
    (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
  have hs := (C.exactAt_iff' 0 1 2 (by simp) (by simp)).mp he
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hs

end GlobalTheory.LineBundleSections
