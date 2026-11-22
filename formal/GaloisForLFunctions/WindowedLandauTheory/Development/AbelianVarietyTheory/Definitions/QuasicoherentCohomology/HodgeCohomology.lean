import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback

/-! Hodge cohomology over the base ring of a scheme. -/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}}

/-- Hodge cohomology is the sheaf cohomology of the sheaf of relative forms. -/
def HodgeCohomology (s : X ⟶ Spec (CommRingCat.of k)) (p q : ℕ) : Type u :=
  CohomologyOn (relativeForms s p) ⊤ q

instance (s : X ⟶ Spec (CommRingCat.of k)) (p q : ℕ) : AddCommGroup (HodgeCohomology s p q) :=
  inferInstanceAs (AddCommGroup (CohomologyOn (relativeForms s p) ⊤ q))

instance (s : X ⟶ Spec (CommRingCat.of k)) (p q : ℕ) : Module k (HodgeCohomology s p q) :=
  letI : Algebra k Γ(X, ⊤) := sectionAlgebra s ⊤
  Module.compHom (CohomologyOn (relativeForms s p) ⊤ q) (algebraMap k Γ(X, ⊤))

/-- Pullback of relative forms induces a base-linear map on Hodge cohomology. -/
def hodgePullback {R : Type} [CommRing R] {A B : Scheme.{0}}
    {s : A ⟶ Spec (CommRingCat.of R)} {t : B ⟶ Spec (CommRingCat.of R)}
    {f : B ⟶ A} (hf : f ≫ s = t) (p q : ℕ) :
    HodgeCohomology s p q →ₗ[R] HodgeCohomology t p q :=
  let L := CohomologyOn.pullback f (relativeFormsPullback hf p) ⊤ q
  { L.toAddMonoidHom with
    map_smul' r v := by
      letI : Algebra R Γ(A, ⊤) := sectionAlgebra s ⊤
      letI : Algebra R Γ(B, ⊤) := sectionAlgebra t ⊤
      change L (algebraMap R Γ(A, ⊤) r •
          (show CohomologyOn (relativeForms s p) ⊤ q from v)) =
        algebraMap R Γ(B, ⊤) r • L v
      rw [L.map_smulₛₗ]
      exact congrArg (fun a : Γ(B, ⊤) => a • L v) ((sectionPullback hf ⊤).commutes r) }

end GlobalTheory.SchemeCohomology
