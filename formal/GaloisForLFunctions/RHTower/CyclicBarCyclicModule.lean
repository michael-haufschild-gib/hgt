import GaloisForLFunctions.RHTower.CyclicBarCyclicLinearRelations

/-!
# Genuine cyclic bar module

The tensor powers of any unital possibly noncommutative `R`-algebra, with the explicit bar faces,
unit degeneracies, and right rotation, form a cyclic module on the exact generator-and-relation
presentation of the simplex category.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Unnormalized cyclic bar module of a unital possibly noncommutative algebra. -/
def cyclicBarCyclicModule : CyclicModule R where
  simplicial := cyclicBarPresentedSimplicial (R := R) (A := A)
  cyclic n := ModuleCat.ofHom (cyclicBarRotate (R := R) (A := A) n).toLinearMap
  cyclic_order n := cyclicBar_categoricalRotate_order (R := R) (A := A) n
  cyclic_face_zero n := by
    apply ModuleCat.hom_ext
    change (cyclicBarFace (R := R) (A := A) 0).comp
        (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap = _
    exact cyclicBarRotate_comp_face_zero (R := R) (A := A)
  cyclic_face_succ n i := by
    apply ModuleCat.hom_ext
    change (cyclicBarFace (R := R) (A := A) i.succ).comp
        (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap = _
    exact cyclicBarRotate_comp_face_succ (R := R) (A := A) i
  cyclic_degeneracy_zero n := by
    apply ModuleCat.hom_ext
    change (cyclicBarDegeneracy (R := R) (A := A) 0).comp
        (cyclicBarRotate (R := R) (A := A) n).toLinearMap = _
    exact cyclicBarRotate_comp_degeneracy_zero (R := R) (A := A)
  cyclic_degeneracy_succ n i := by
    apply ModuleCat.hom_ext
    change (cyclicBarDegeneracy (R := R) (A := A) i.succ).comp
        (cyclicBarRotate (R := R) (A := A) n).toLinearMap = _
    exact cyclicBarRotate_comp_degeneracy_succ (R := R) (A := A) i

@[simp]
theorem cyclicBarCyclicModule_degree (n : ℕ) :
    (cyclicBarCyclicModule (R := R) (A := A)).simplicial.degree n =
      ModuleCat.of R (CyclicBarTensor R A n) :=
  rfl

@[simp]
theorem cyclicBarCyclicModule_δ {n : ℕ} (i : Fin (n + 2)) :
    (cyclicBarCyclicModule (R := R) (A := A)).simplicial.δ i =
      ModuleCat.ofHom (cyclicBarFace (R := R) (A := A) i) :=
  rfl

@[simp]
theorem cyclicBarCyclicModule_σ {n : ℕ} (i : Fin (n + 1)) :
    (cyclicBarCyclicModule (R := R) (A := A)).simplicial.σ i =
      ModuleCat.ofHom (cyclicBarDegeneracy (R := R) (A := A) i) :=
  rfl

@[simp]
theorem cyclicBarCyclicModule_cyclic (n : ℕ) :
    (cyclicBarCyclicModule (R := R) (A := A)).cyclic n =
      ModuleCat.ofHom (cyclicBarRotate (R := R) (A := A) n).toLinearMap :=
  rfl

end RHTower
end GaloisForLFunctions
