import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveCoherentFiniteness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsFinite
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineModulePushforward
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgeTrace

/-! The relative forms of a projective scheme have finite-dimensional cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry

namespace GlobalTheory.SchemeCohomology

open UpperTheory.Cb

/-- Direct image along a projective embedding reduces Hodge finiteness to
coherent cohomology on projective space. -/
theorem hodgeCohomology_finite_of_projective {K : Type} [Field K] {X : Scheme.{0}}
    (s : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType s]
    (h : IsProjOver s) (p q : ℕ) : Module.Finite K (HodgeCohomology s p q) := by
  obtain ⟨N, i, hi, ht⟩ := h
  letI := hi
  let F := relativeForms s p
  let J := (Scheme.Modules.pushforward i).obj F
  letI : F.IsQuasicoherent := relativeForms_isQuasicoherent s p
  letI : J.IsQuasicoherent := pushforward_isQuasicoherent i F
  have hfin (j : Fin (N + 1)) :
      Module.Finite Γ(PSpace K N, PSpace.coordinateOpen K N j) Γ(J, PSpace.coordinateOpen K N j) := by
    have hU := PSpace.isAffineOpen_coordinateInter K N (Finset.singleton_nonempty j)
    rw [coverInter_singleton, top_inf_eq] at hU
    letI := relativeForms_sections_finite s (hU.preimage i) p
    exact pushforward_sections_finite i F hU
  letI := sectionAlgebra (PSpace.str K N) ⊤
  letI := Module.compHom (PushforwardFormsCohomology s i p q) (algebraMap K Γ(PSpace K N, ⊤))
  letI := pspace_cohomologyFinite K N J hfin q
  exact Module.Finite.equiv (formsPushforwardEquiv ht p q)

end GlobalTheory.SchemeCohomology
