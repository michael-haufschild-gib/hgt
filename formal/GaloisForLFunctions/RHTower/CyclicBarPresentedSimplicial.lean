import GaloisForLFunctions.RHTower.CyclicBarSimplicialLinearRelations
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Presented simplicial module of a noncommutative algebra

The face and degeneracy tensor operators define a prefunctor on the free simplex quiver.  The six
proved linear identities certify that it kills the generating relation, so it descends to the
quotient presentation `SimplexCategoryGenRel`.  Taking the left opposite gives the required
contravariant simplicial module.  No equivalence with mathlib's unfinished simplex presentation is
assumed.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Cyclic-bar tensors and their explicit operators as a prefunctor on the free simplex quiver. -/
def cyclicBarFreePrefunctor : Prefunctor FreeSimplexQuiver (ModuleCat R)ᵒᵖ where
  obj n := Opposite.op (ModuleCat.of R (CyclicBarTensor R A n))
  map f := match f with
    | FreeSimplexQuiver.Hom.δ i =>
        (ModuleCat.ofHom (cyclicBarFace (R := R) (A := A) i)).op
    | FreeSimplexQuiver.Hom.σ i =>
        (ModuleCat.ofHom (cyclicBarDegeneracy (R := R) (A := A) i)).op

/-- Covariant functor to opposite modules obtained by quotienting the free quiver by all
simplicial identities. -/
def cyclicBarCovariantOpposite : SimplexCategoryGenRel ⥤ (ModuleCat R)ᵒᵖ :=
  CategoryTheory.Quotient.lift _
    (Paths.lift (cyclicBarFreePrefunctor (R := R) (A := A)))
    (fun _ _ _ _ h ↦ match h with
      | .δ_comp_δ H => by
          apply Quiver.Hom.unop_inj
          apply ModuleCat.hom_ext
          change (cyclicBarFace (R := R) (A := A) _).comp
              (cyclicBarFace (R := R) (A := A) _) = _
          exact cyclicBarFace_comp_face (R := R) (A := A) _ _ H
      | .δ_comp_σ_of_le H => by
          apply Quiver.Hom.unop_inj
          apply ModuleCat.hom_ext
          change (cyclicBarFace (R := R) (A := A) _).comp
              (cyclicBarDegeneracy (R := R) (A := A) _) = _
          exact cyclicBarFace_comp_degeneracy_of_le (R := R) (A := A) _ _ H
      | .δ_comp_σ_self => by
          apply Quiver.Hom.unop_inj
          apply ModuleCat.hom_ext
          change (cyclicBarFace (R := R) (A := A) _).comp
              (cyclicBarDegeneracy (R := R) (A := A) _) = LinearMap.id
          exact cyclicBarFace_comp_degeneracy_self (R := R) (A := A) _
      | .δ_comp_σ_succ => by
          apply Quiver.Hom.unop_inj
          apply ModuleCat.hom_ext
          change (cyclicBarFace (R := R) (A := A) _).comp
              (cyclicBarDegeneracy (R := R) (A := A) _) = LinearMap.id
          exact cyclicBarFace_comp_degeneracy_succ (R := R) (A := A) _
      | .δ_comp_σ_of_gt H => by
          apply Quiver.Hom.unop_inj
          apply ModuleCat.hom_ext
          change (cyclicBarFace (R := R) (A := A) _).comp
              (cyclicBarDegeneracy (R := R) (A := A) _) = _
          exact cyclicBarFace_comp_degeneracy_of_gt (R := R) (A := A) _ _ H
      | .σ_comp_σ H => by
          apply Quiver.Hom.unop_inj
          apply ModuleCat.hom_ext
          change (cyclicBarDegeneracy (R := R) (A := A) _).comp
              (cyclicBarDegeneracy (R := R) (A := A) _) = _
          exact cyclicBarDegeneracy_comp_degeneracy (R := R) (A := A) _ _ H)

/-- Genuine tensor cyclic bar as a presented simplicial `R`-module. -/
def cyclicBarPresentedSimplicial : PresentedSimplicialObject (ModuleCat R) :=
  (cyclicBarCovariantOpposite (R := R) (A := A)).leftOp

@[simp]
theorem cyclicBarPresentedSimplicial_degree (n : ℕ) :
    (cyclicBarPresentedSimplicial (R := R) (A := A)).degree n =
      ModuleCat.of R (CyclicBarTensor R A n) :=
  rfl

@[simp]
theorem cyclicBarPresentedSimplicial_δ {n : ℕ} (i : Fin (n + 2)) :
    (cyclicBarPresentedSimplicial (R := R) (A := A)).δ i =
      ModuleCat.ofHom (cyclicBarFace (R := R) (A := A) i) :=
  rfl

@[simp]
theorem cyclicBarPresentedSimplicial_σ {n : ℕ} (i : Fin (n + 1)) :
    (cyclicBarPresentedSimplicial (R := R) (A := A)).σ i =
      ModuleCat.ofHom (cyclicBarDegeneracy (R := R) (A := A) i) :=
  rfl

end RHTower
end GaloisForLFunctions
