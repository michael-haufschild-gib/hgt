import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistGlobalSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistTopFiniteness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistQuasicoherent

/-! Linear Čech comparison gives finite cohomology for negative projective twists. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry TopologicalSpace

namespace GlobalTheory.SchemeCohomology

open UpperTheory.Cb

variable (K : Type) [Field K] (N : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

theorem pspaceTwist_isQuasicoherent (k : ℤ) : (pspaceTwist K N k).IsQuasicoherent :=
  ProjTwist.twistingSheaf_isQuasicoherent (MvPolynomial.isHomogeneous_X K)
    (PSpace.iSup_coordinateOpen K N) k

/-- Cohomology on a projective space is computed by its coordinate charts. -/
def pspaceCechLinearEquiv (F : (PSpace K N).Modules) [F.IsQuasicoherent] (q : ℕ) :
    ModuleCechCohomology ⊤ (PSpace.coordinateOpen K N) F q ≃ₗ[Γ(PSpace K N, ⊤)]
      CohomologyOn F ⊤ q := by
  have e := moduleLerayLinearEquiv ⊤ (PSpace.coordinateOpen K N) F q
    (PSpace.iSup_coordinateOpen K N).ge
    (fun a ha => quasicoherent_acyclicOn F (PSpace.isAffineOpen_coordinateInter K N ha))
  rwa [coverInter_empty] at e

private theorem pspaceCech_eq_zero_of_exact (F : (PSpace K N).Modules) (q : ℕ)
    (h : (sheafCech ((SheafOfModules.toSheaf (PSpace K N).ringCatSheaf).obj F)
      ⊤ (PSpace.coordinateOpen K N)).ExactAt (q + 1))
    (x : ModuleCechCohomology ⊤ (PSpace.coordinateOpen K N) F (q + 1)) : x = 0 := by
  have hz := (FinsetCechDatum.cochainComplex_exactAt _ h).isZero_homology
  exact ConcreteCategory.congr_hom (hz.eq_of_src (𝟙 _) 0) x

private theorem pspaceCech_eq_zero_above (F : (PSpace K N).Modules) (q : ℕ) (hq : N < q + 1)
    (x : ModuleCechCohomology ⊤ (PSpace.coordinateOpen K N) F (q + 1)) : x = 0 :=
  pspaceCech_eq_zero_of_exact K N F q
    (FinsetCechDatum.exactAt_of_card_lt _ (by simpa using Nat.succ_lt_succ hq)) x

/-- Quasi-coherent cohomology vanishes above the projective dimension. -/
theorem pspaceCohomology_eq_zero_above (F : (PSpace K N).Modules) [F.IsQuasicoherent]
    (q : ℕ) (hq : N < q + 1) (x : CohomologyOn F ⊤ (q + 1)) : x = 0 := by
  obtain ⟨a, rfl⟩ := (pspaceCechLinearEquiv K N F (q + 1)).surjective x
  rw [pspaceCech_eq_zero_above K N F q hq a, map_zero]

private theorem pspaceTwist_cechFinite (m q : ℕ) :
    letI := sectionAlgebra (PSpace.str K N) ⊤
    let H := ModuleCechCohomology ⊤ (PSpace.coordinateOpen K N) (pspaceTwist K N (-(m : ℤ))) q
    letI := Module.compHom H (algebraMap K Γ(PSpace K N, ⊤))
    Module.Finite K H := by
  cases q with
  | zero => exact pspaceTwist_zeroCech_finite K N m
  | succ q =>
    letI := sectionAlgebra (PSpace.str K N) ⊤
    let H := ModuleCechCohomology ⊤ (PSpace.coordinateOpen K N) (pspaceTwist K N (-(m : ℤ))) (q + 1)
    letI := Module.compHom H (algebraMap K Γ(PSpace K N, ⊤))
    rcases lt_trichotomy (q + 1) N with h | rfl | h
    · have hz := pspaceCech_eq_zero_of_exact K N (pspaceTwist K N (-(m : ℤ))) q
        (pspaceTwistCech_exactAt_below_top K N m q h)
      letI : Subsingleton H := ⟨fun x y => (hz x).trans (hz y).symm⟩
      change Module.Finite K H
      infer_instance
    · exact pspaceTwist_topCech_finite K q m
    · have hz := pspaceCech_eq_zero_above K N (pspaceTwist K N (-(m : ℤ))) q h
      letI : Subsingleton H := ⟨fun x y => (hz x).trans (hz y).symm⟩
      change Module.Finite K H
      infer_instance

/-- Negative twists on projective space have finite-dimensional cohomology in every degree. -/
theorem pspaceTwist_cohomologyFinite (m q : ℕ) :
    letI := sectionAlgebra (PSpace.str K N) ⊤
    let H := CohomologyOn (pspaceTwist K N (-(m : ℤ))) ⊤ q
    letI := Module.compHom H (algebraMap K Γ(PSpace K N, ⊤))
    Module.Finite K H := by
  letI := sectionAlgebra (PSpace.str K N) ⊤
  let F := pspaceTwist K N (-(m : ℤ))
  letI : F.IsQuasicoherent := pspaceTwist_isQuasicoherent K N _
  let A := ModuleCechCohomology ⊤ (PSpace.coordinateOpen K N) F q
  let B := CohomologyOn F ⊤ q
  letI : Module K A := Module.compHom A (algebraMap K Γ(PSpace K N, ⊤))
  letI : Module K B := Module.compHom B (algebraMap K Γ(PSpace K N, ⊤))
  haveI : Module.Finite K A := pspaceTwist_cechFinite K N m q
  let e := pspaceCechLinearEquiv K N F q
  exact Module.Finite.of_surjective
    ({ e.toAddMonoidHom with map_smul' := fun r x => e.map_smul (algebraMap K Γ(PSpace K N, ⊤) r) x } :
      A →ₗ[K] B) e.surjective

end GlobalTheory.SchemeCohomology
