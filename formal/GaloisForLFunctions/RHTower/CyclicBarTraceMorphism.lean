import GaloisForLFunctions.RHTower.CyclicBarTraceAugmentation

/-!
# A trace induces a morphism of genuine cyclic modules

The scalar module, constant in every degree with identity faces, degeneracies, and rotations, is a
cyclic module.  Every linear trace on a unital algebra induces a morphism from the genuine tensor
cyclic bar module to this scalar cyclic module.  Naturality is proved for every morphism in the
generator-and-relation simplex category, not only for its generating operators.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower

universe u

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]

/-! ## Constant scalar cyclic module -/

/-- Constant presented simplicial module with value the rank-one scalar module. -/
def scalarConstantPresentedSimplicial :
    PresentedSimplicialObject (ModuleCat R) :=
  (Functor.const SimplexCategoryGenRelᵒᵖ).obj (ModuleCat.of R R)

@[simp]
theorem scalarConstantPresentedSimplicial_degree (n : ℕ) :
    (scalarConstantPresentedSimplicial (R := R)).degree n = ModuleCat.of R R :=
  rfl

@[simp]
theorem scalarConstantPresentedSimplicial_map {j k : SimplexCategoryGenRelᵒᵖ}
    (f : j ⟶ k) :
    (scalarConstantPresentedSimplicial (R := R)).map f = 𝟙 _ :=
  rfl

/-- Constant scalar cyclic module. -/
def scalarConstantCyclicModule : CyclicModule R where
  simplicial := scalarConstantPresentedSimplicial (R := R)
  cyclic _ := 𝟙 _
  cyclic_order n := by
    change categoricalEndIterate (𝟙 (ModuleCat.of R R)) (n + 1) = 𝟙 _
    induction n + 1 with
    | zero => rfl
    | succ n ih => simp [categoricalEndIterate, ih]
  cyclic_face_zero n := by simp
  cyclic_face_succ n i := by simp
  cyclic_degeneracy_zero n := by simp
  cyclic_degeneracy_succ n i := by simp

@[simp]
theorem scalarConstantCyclicModule_cyclic (n : ℕ) :
    (scalarConstantCyclicModule (R := R)).cyclic n = 𝟙 _ :=
  rfl

/-! ## Simplicial and cyclic trace morphisms -/

/-- Component of the trace augmentation at an arbitrary object of the presented simplex
category. -/
def cyclicBarTraceComponent (τ : A →ₗ[R] R) :
    ∀ a : SimplexCategoryGenRel,
      (cyclicBarPresentedSimplicial (R := R) (A := A)).obj (Opposite.op a) ⟶
        ModuleCat.of R R :=
  SimplexCategoryGenRel.rec fun n ↦
    ModuleCat.ofHom (cyclicBarTraceAugmentation τ n)

@[simp]
theorem cyclicBarTraceComponent_mk (τ : A →ₗ[R] R) (n : ℕ) :
    cyclicBarTraceComponent τ (.mk n) =
      ModuleCat.ofHom (cyclicBarTraceAugmentation τ n) :=
  rfl

/-- Trace augmentation is natural for every morphism in the presented simplex category. -/
theorem cyclicBarTraceAugmentation_naturality
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    (cyclicBarPresentedSimplicial (R := R) (A := A)).map f.op ≫
        cyclicBarTraceComponent τ a =
      cyclicBarTraceComponent τ b := by
  let P : MorphismProperty SimplexCategoryGenRel := fun a b f ↦
    (cyclicBarPresentedSimplicial (R := R) (A := A)).map f.op ≫
        cyclicBarTraceComponent τ a =
      cyclicBarTraceComponent τ b
  apply SimplexCategoryGenRel.hom_induction P
  · intro n
    dsimp [P]
    simp
  · intro n m u i hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map u.op ≫
          cyclicBarTraceComponent τ (.mk n) =
        cyclicBarTraceComponent τ (.mk m) at hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map
            ((SimplexCategoryGenRel.δ i).op ≫ u.op) ≫
          cyclicBarTraceComponent τ (.mk n) =
        cyclicBarTraceComponent τ (.mk (m + 1))
    rw [Functor.map_comp, Category.assoc, hu]
    change
      ModuleCat.ofHom (cyclicBarFace (R := R) (A := A) i) ≫
          ModuleCat.ofHom (cyclicBarTraceAugmentation τ m) =
        ModuleCat.ofHom (cyclicBarTraceAugmentation τ (m + 1))
    apply ModuleCat.hom_ext
    exact cyclicBarTraceAugmentation_comp_face τ hτ m i
  · intro n m u i hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map u.op ≫
          cyclicBarTraceComponent τ (.mk n) =
        cyclicBarTraceComponent τ (.mk (m + 1)) at hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map
            ((SimplexCategoryGenRel.σ i).op ≫ u.op) ≫
          cyclicBarTraceComponent τ (.mk n) =
        cyclicBarTraceComponent τ (.mk m)
    rw [Functor.map_comp, Category.assoc, hu]
    change
      ModuleCat.ofHom (cyclicBarDegeneracy (R := R) (A := A) i) ≫
          ModuleCat.ofHom (cyclicBarTraceAugmentation τ (m + 1)) =
        ModuleCat.ofHom (cyclicBarTraceAugmentation τ m)
    apply ModuleCat.hom_ext
    exact cyclicBarTraceAugmentation_comp_degeneracy τ m i

/-- Natural transformation underlying the cyclic morphism induced by a trace. -/
def cyclicBarTraceSimplicialHom
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    (cyclicBarCyclicModule (R := R) (A := A)).simplicial ⟶
      (scalarConstantCyclicModule (R := R)).simplicial where
  app j := cyclicBarTraceComponent τ j.unop
  naturality {j k} f := by
    have h := cyclicBarTraceAugmentation_naturality τ hτ f.unop
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map f ≫
          cyclicBarTraceComponent τ k.unop =
        cyclicBarTraceComponent τ j.unop ≫ 𝟙 _
    rw [Category.comp_id]
    exact h

@[simp]
theorem cyclicBarTraceSimplicialHom_app
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a)) (n : ℕ) :
    (cyclicBarTraceSimplicialHom τ hτ).app (.op (.mk n)) =
      ModuleCat.ofHom (cyclicBarTraceAugmentation τ n) :=
  rfl

/-- Genuine cyclic-module morphism induced by a linear trace. -/
def cyclicBarTraceCyclicHom
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    CyclicModule.Hom (cyclicBarCyclicModule (R := R) (A := A))
      (scalarConstantCyclicModule (R := R)) where
  simplicial := cyclicBarTraceSimplicialHom τ hτ
  cyclic_naturality n := by
    simp only [cyclicBarCyclicModule_cyclic,
      cyclicBarTraceSimplicialHom_app,
      scalarConstantCyclicModule_cyclic, Category.comp_id]
    apply ModuleCat.hom_ext
    change
      (cyclicBarTraceAugmentation τ n).comp
          (cyclicBarRotate (R := R) (A := A) n).toLinearMap =
        cyclicBarTraceAugmentation τ n
    exact cyclicBarTraceAugmentation_comp_rotate τ hτ n

end RHTower
end GaloisForLFunctions
