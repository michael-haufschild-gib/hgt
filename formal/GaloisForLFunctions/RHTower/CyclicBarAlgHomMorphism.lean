import GaloisForLFunctions.RHTower.CyclicBarCyclicModule

/-!
# Functoriality of the genuine cyclic bar module

An algebra homomorphism induces tensor-power maps in every degree.  This file proves compatibility
with every face, degeneracy, and cyclic rotation, promotes generator compatibility to naturality
for the full presented simplex category, and packages the result as a genuine cyclic-module
morphism.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace GaloisForLFunctions
namespace RHTower

universe u v

variable {R : Type u} {A B : Type v} [CommRing R]
  [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- Degreewise tensor power of an algebra homomorphism. -/
def cyclicBarAlgHomDegree (φ : A →ₐ[R] B) (n : ℕ) :
    CyclicBarTensor R A n →ₗ[R] CyclicBarTensor R B n :=
  PiTensorProduct.map fun _ : Fin (n + 1) => φ.toLinearMap

@[simp]
theorem cyclicBarAlgHomDegree_tprod (φ : A →ₐ[R] B) (n : ℕ)
    (x : Fin (n + 1) → A) :
    cyclicBarAlgHomDegree φ n (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i => φ (x i)) := by
  simp [cyclicBarAlgHomDegree]

theorem cyclicBarAlgHom_face_tuple (φ : A →ₐ[R] B) {n : ℕ}
    (i : Fin (n + 2)) (x : Fin (n + 2) → A) :
    (fun j => φ (cyclicBarFaceTuple i x j)) =
      cyclicBarFaceTuple i (fun j => φ (x j)) := by
  funext j
  induction i using Fin.lastCases with
  | last =>
      by_cases hj : j = 0
      · subst j
        simp [cyclicBarFaceTuple, cyclicBarFaceWrapTuple]
      · simp [cyclicBarFaceTuple, cyclicBarFaceWrapTuple, hj,
          Fin.init]
  | cast i =>
      by_cases hj : j = i
      · subst j
        simp [cyclicBarFaceTuple, cyclicBarFaceNonwrapTuple]
      · simp [cyclicBarFaceTuple, cyclicBarFaceNonwrapTuple, hj,
          Fin.removeNth]

theorem cyclicBarAlgHom_degeneracy_tuple (φ : A →ₐ[R] B) {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → A) :
    (fun j => φ (cyclicBarDegeneracyTuple i x j)) =
      cyclicBarDegeneracyTuple i (fun j => φ (x j)) := by
  funext j
  cases j using i.succ.succAboveCases with
  | x => simp [cyclicBarDegeneracyTuple]
  | p j => simp [cyclicBarDegeneracyTuple]

theorem cyclicBarAlgHom_rotate_tuple (φ : A →ₐ[R] B) {n : ℕ}
    (x : Fin (n + 1) → A) :
    (fun j => φ (cyclicBarRotateTuple x j)) =
      cyclicBarRotateTuple (fun j => φ (x j)) :=
  rfl

theorem cyclicBarAlgHom_comp_face (φ : A →ₐ[R] B) {n : ℕ}
    (i : Fin (n + 2)) :
    (cyclicBarAlgHomDegree φ n).comp
        (cyclicBarFace (R := R) (A := A) i) =
      (cyclicBarFace (R := R) (A := B) i).comp
        (cyclicBarAlgHomDegree φ (n + 1)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change cyclicBarAlgHomDegree φ n
      (cyclicBarFace (R := R) (A := A) i (PiTensorProduct.tprod R x)) =
    cyclicBarFace (R := R) (A := B) i
      (cyclicBarAlgHomDegree φ (n + 1) (PiTensorProduct.tprod R x))
  rw [cyclicBarFace_tprod, cyclicBarAlgHomDegree_tprod,
    cyclicBarAlgHomDegree_tprod, cyclicBarFace_tprod,
    cyclicBarAlgHom_face_tuple]

theorem cyclicBarAlgHom_comp_degeneracy (φ : A →ₐ[R] B) {n : ℕ}
    (i : Fin (n + 1)) :
    (cyclicBarAlgHomDegree φ (n + 1)).comp
        (cyclicBarDegeneracy (R := R) (A := A) i) =
      (cyclicBarDegeneracy (R := R) (A := B) i).comp
        (cyclicBarAlgHomDegree φ n) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change cyclicBarAlgHomDegree φ (n + 1)
      (cyclicBarDegeneracy (R := R) (A := A) i (PiTensorProduct.tprod R x)) =
    cyclicBarDegeneracy (R := R) (A := B) i
      (cyclicBarAlgHomDegree φ n (PiTensorProduct.tprod R x))
  rw [cyclicBarDegeneracy_tprod, cyclicBarAlgHomDegree_tprod,
    cyclicBarAlgHomDegree_tprod, cyclicBarDegeneracy_tprod,
    cyclicBarAlgHom_degeneracy_tuple]

theorem cyclicBarAlgHom_comp_rotate (φ : A →ₐ[R] B) (n : ℕ) :
    (cyclicBarAlgHomDegree φ n).comp
        (cyclicBarRotate (R := R) (A := A) n).toLinearMap =
      (cyclicBarRotate (R := R) (A := B) n).toLinearMap.comp
        (cyclicBarAlgHomDegree φ n) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change cyclicBarAlgHomDegree φ n
      (cyclicBarRotate (R := R) (A := A) n (PiTensorProduct.tprod R x)) =
    cyclicBarRotate (R := R) (A := B) n
      (cyclicBarAlgHomDegree φ n (PiTensorProduct.tprod R x))
  rw [cyclicBarRotate_tprod, cyclicBarAlgHomDegree_tprod,
    cyclicBarAlgHomDegree_tprod, cyclicBarRotate_tprod,
    cyclicBarAlgHom_rotate_tuple]

/-- Component at an arbitrary object of the presented simplex category. -/
def cyclicBarAlgHomComponent (φ : A →ₐ[R] B) :
    ∀ a : SimplexCategoryGenRel,
      (cyclicBarPresentedSimplicial (R := R) (A := A)).obj (.op a) ⟶
        (cyclicBarPresentedSimplicial (R := R) (A := B)).obj (.op a) :=
  SimplexCategoryGenRel.rec fun n =>
    ModuleCat.ofHom (cyclicBarAlgHomDegree φ n)

@[simp]
theorem cyclicBarAlgHomComponent_mk (φ : A →ₐ[R] B) (n : ℕ) :
    cyclicBarAlgHomComponent φ (.mk n) =
      ModuleCat.ofHom (cyclicBarAlgHomDegree φ n) :=
  rfl

theorem cyclicBarAlgHom_naturality (φ : A →ₐ[R] B)
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    (cyclicBarPresentedSimplicial (R := R) (A := A)).map f.op ≫
        cyclicBarAlgHomComponent φ a =
      cyclicBarAlgHomComponent φ b ≫
        (cyclicBarPresentedSimplicial (R := R) (A := B)).map f.op := by
  let P : MorphismProperty SimplexCategoryGenRel := fun a b f =>
    (cyclicBarPresentedSimplicial (R := R) (A := A)).map f.op ≫
        cyclicBarAlgHomComponent φ a =
      cyclicBarAlgHomComponent φ b ≫
        (cyclicBarPresentedSimplicial (R := R) (A := B)).map f.op
  apply SimplexCategoryGenRel.hom_induction P
  · intro n
    dsimp [P]
    simp
  · intro n m u i hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map u.op ≫
          cyclicBarAlgHomComponent φ (.mk n) =
        cyclicBarAlgHomComponent φ (.mk m) ≫
          (cyclicBarPresentedSimplicial (R := R) (A := B)).map u.op at hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map
            ((SimplexCategoryGenRel.δ i).op ≫ u.op) ≫
          cyclicBarAlgHomComponent φ (.mk n) =
        cyclicBarAlgHomComponent φ (.mk (m + 1)) ≫
          (cyclicBarPresentedSimplicial (R := R) (A := B)).map
            ((SimplexCategoryGenRel.δ i).op ≫ u.op)
    have hface :
        (cyclicBarPresentedSimplicial (R := R) (A := A)).map
              (SimplexCategoryGenRel.δ i).op ≫
            cyclicBarAlgHomComponent φ (.mk m) =
          cyclicBarAlgHomComponent φ (.mk (m + 1)) ≫
            (cyclicBarPresentedSimplicial (R := R) (A := B)).map
              (SimplexCategoryGenRel.δ i).op := by
      apply ModuleCat.hom_ext
      exact cyclicBarAlgHom_comp_face φ i
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hu,
      ← Category.assoc, hface, Category.assoc]
  · intro n m u i hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map u.op ≫
          cyclicBarAlgHomComponent φ (.mk n) =
        cyclicBarAlgHomComponent φ (.mk (m + 1)) ≫
          (cyclicBarPresentedSimplicial (R := R) (A := B)).map u.op at hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map
            ((SimplexCategoryGenRel.σ i).op ≫ u.op) ≫
          cyclicBarAlgHomComponent φ (.mk n) =
        cyclicBarAlgHomComponent φ (.mk m) ≫
          (cyclicBarPresentedSimplicial (R := R) (A := B)).map
            ((SimplexCategoryGenRel.σ i).op ≫ u.op)
    have hdegeneracy :
        (cyclicBarPresentedSimplicial (R := R) (A := A)).map
              (SimplexCategoryGenRel.σ i).op ≫
            cyclicBarAlgHomComponent φ (.mk (m + 1)) =
          cyclicBarAlgHomComponent φ (.mk m) ≫
            (cyclicBarPresentedSimplicial (R := R) (A := B)).map
              (SimplexCategoryGenRel.σ i).op := by
      apply ModuleCat.hom_ext
      exact cyclicBarAlgHom_comp_degeneracy φ i
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hu,
      ← Category.assoc, hdegeneracy, Category.assoc]

/-- Natural transformation on the full presented simplicial modules. -/
def cyclicBarAlgHomSimplicialHom (φ : A →ₐ[R] B) :
    (cyclicBarCyclicModule (R := R) (A := A)).simplicial ⟶
      (cyclicBarCyclicModule (R := R) (A := B)).simplicial where
  app j := cyclicBarAlgHomComponent φ j.unop
  naturality {_ _} f := cyclicBarAlgHom_naturality φ f.unop

@[simp]
theorem cyclicBarAlgHomSimplicialHom_app (φ : A →ₐ[R] B) (n : ℕ) :
    (cyclicBarAlgHomSimplicialHom φ).app (.op (.mk n)) =
      ModuleCat.ofHom (cyclicBarAlgHomDegree φ n) :=
  rfl

/-- Genuine cyclic-module morphism induced by an algebra homomorphism. -/
def cyclicBarAlgHomCyclicHom (φ : A →ₐ[R] B) :
    CyclicModule.Hom (cyclicBarCyclicModule (R := R) (A := A))
      (cyclicBarCyclicModule (R := R) (A := B)) where
  simplicial := cyclicBarAlgHomSimplicialHom φ
  cyclic_naturality n := by
    simp only [cyclicBarCyclicModule_cyclic,
      cyclicBarAlgHomSimplicialHom_app]
    apply ModuleCat.hom_ext
    exact cyclicBarAlgHom_comp_rotate φ n

end RHTower
end GaloisForLFunctions
