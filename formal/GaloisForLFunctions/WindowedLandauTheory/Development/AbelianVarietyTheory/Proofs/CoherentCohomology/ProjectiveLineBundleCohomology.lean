import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.NoetherianProjectiveCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleAffineSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineModulePushforward
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsPushforward

/-! Line-bundle cohomology on a projective scheme over a Noetherian base is finite. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

open GlobalTheory.SchemeCohomology UpperTheory.Cb

/-- Push the line bundle forward to projective space and compare cohomology along the closed immersion. -/
theorem cohomology_finite_of_projective {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) (hf : IsProjOver f) {L : LB X} (hL : L.IsLB) (q : ℕ) :
    letI := sectionAlgebra f ⊤
    let H := CohomologyOn (toMod L) ⊤ q
    letI := Module.compHom H (algebraMap R Γ(X, ⊤))
    Module.Finite R H := by
  obtain ⟨N, i, hi, ht⟩ := hf
  letI := hi
  let Y := PSpace R N
  let t := PSpace.str R N
  let F := toMod L
  let J := (Scheme.Modules.pushforward i).obj F
  letI : F.IsQuasicoherent := isQuasicoherent_toMod hL
  letI : J.IsQuasicoherent := pushforward_isQuasicoherent i F
  have hfin (j : Fin (N + 1)) :
      Module.Finite Γ(Y, PSpace.coordinateOpen R N j) Γ(J, PSpace.coordinateOpen R N j) := by
    have hU := PSpace.isAffineOpen_coordinateInter R N (Finset.singleton_nonempty j)
    rw [coverInter_singleton, top_inf_eq] at hU
    letI := (finite_projective_sections hL (hU.preimage i)).1
    exact pushforward_sections_finite i F hU
  let A := CohomologyOn J ⊤ q
  let B := CohomologyOn F ⊤ q
  letI := sectionAlgebra t ⊤
  letI := sectionAlgebra f ⊤
  letI : Module R A := Module.compHom A (algebraMap R Γ(Y, ⊤))
  letI : Module R B := Module.compHom B (algebraMap R Γ(X, ⊤))
  letI : Module.Finite R A := RingPolynomialCech.pspace_cohomologyFinite R N J hfin q
  let C := CohomologyOn.pushforwardComparison i F ⊤ q
  let map : A →ₗ[R] B :=
    { C.toAddMonoidHom with
      map_smul' r x := by
        change C (algebraMap R Γ(Y, ⊤) r • x) = algebraMap R Γ(X, ⊤) r • C x
        exact (C.map_smulₛₗ (algebraMap R Γ(Y, ⊤) r) x).trans
          (congrArg (fun a : Γ(X, ⊤) => a • C x) ((sectionPullback ht ⊤).commutes r)) }
  exact Module.Finite.of_surjective map (quasicoherent_pushforwardComparison_bijective i F q ⊤).2

end GlobalTheory.LineBundleSections
