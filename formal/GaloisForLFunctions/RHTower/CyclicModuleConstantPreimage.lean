import GaloisForLFunctions.RHTower.KRealCyclicModule

/-!
# Constant cyclic modules and submodule preimages

A cyclic morphism into a constant module pulls every fixed submodule of that coefficient module
back to a genuine cyclic submodule.  This is the categorical construction needed for CCM's
strong trace condition: only the diagonal scalar trace is constrained, while operator-valued
chains remain in the ambient cyclic bar.
-/

noncomputable section

open CategoryTheory

universe u v

namespace GaloisForLFunctions
namespace RHTower

variable {R : Type u} [CommRing R]

/-- Constant presented simplicial module with arbitrary coefficient module `M`. -/
def moduleConstantPresentedSimplicial (M : Type v)
    [AddCommGroup M] [Module R M] :
    PresentedSimplicialObject (ModuleCat.{v} R) :=
  (Functor.const SimplexCategoryGenRelᵒᵖ).obj (ModuleCat.of R M)

@[simp]
theorem moduleConstantPresentedSimplicial_degree
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (moduleConstantPresentedSimplicial (R := R) M).degree n =
      ModuleCat.of R M :=
  rfl

@[simp]
theorem moduleConstantPresentedSimplicial_map
    (M : Type v) [AddCommGroup M] [Module R M]
    {j k : SimplexCategoryGenRelᵒᵖ} (f : j ⟶ k) :
    (moduleConstantPresentedSimplicial (R := R) M).map f = 𝟙 _ :=
  rfl

/-- Constant cyclic module with arbitrary coefficient module. -/
def moduleConstantCyclicModule (M : Type v)
    [AddCommGroup M] [Module R M] : CyclicModule R where
  simplicial := moduleConstantPresentedSimplicial (R := R) M
  cyclic _ := 𝟙 _
  cyclic_order n := by
    change categoricalEndIterate (𝟙 (ModuleCat.of R M)) (n + 1) = 𝟙 _
    induction n + 1 with
    | zero => rfl
    | succ n ih => simp [categoricalEndIterate, ih]
  cyclic_face_zero n := by simp
  cyclic_face_succ n i := by simp
  cyclic_degeneracy_zero n := by simp
  cyclic_degeneracy_succ n i := by simp

@[simp]
theorem moduleConstantCyclicModule_cyclic
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (moduleConstantCyclicModule (R := R) M).cyclic n = 𝟙 _ :=
  rfl

namespace CyclicModule.Hom

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {X : CyclicModule R}

/-- Degreewise inverse image of a fixed coefficient submodule under a cyclic morphism into a
constant cyclic module. -/
def constantPreimageSubmodule
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) (j : SimplexCategoryGenRelᵒᵖ) :
    Submodule R (X.simplicial.obj j) :=
  P.comap (f.simplicial.app j).hom

@[simp]
theorem mem_constantPreimageSubmodule_iff
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) (j : SimplexCategoryGenRelᵒᵖ)
    (x : X.simplicial.obj j) :
    x ∈ f.constantPreimageSubmodule P j ↔ f.simplicial.app j x ∈ P :=
  Iff.rfl

/-- Presented simplicial object carried by the degreewise inverse images. -/
def constantPreimageSimplicial
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) : PresentedSimplicialObject (ModuleCat.{v} R) where
  obj j := ModuleCat.of R (f.constantPreimageSubmodule P j)
  map {j k} h := ModuleCat.ofHom
    { toFun := fun x => ⟨X.simplicial.map h x.1, by
          rw [f.mem_constantPreimageSubmodule_iff]
          have hx := (f.mem_constantPreimageSubmodule_iff P j x.1).mp x.2
          rw [← ModuleCat.comp_apply, f.simplicial.naturality h,
            ModuleCat.comp_apply]
          change f.simplicial.app j x.1 ∈ P
          exact hx⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }
  map_id j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp
  map_comp {i j k} h l := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp

/-- Inclusion of the inverse-image simplicial module into its ambient cyclic module. -/
def constantPreimageSimplicialInclusion
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) :
    f.constantPreimageSimplicial P ⟶ X.simplicial where
  app j := ModuleCat.ofHom (f.constantPreimageSubmodule P j).subtype
  naturality {j k} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Ambient cyclic rotation restricted to a constant-submodule inverse image. -/
def constantPreimageCyclic
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) (n : ℕ) :
    (f.constantPreimageSimplicial P).degree n ⟶
      (f.constantPreimageSimplicial P).degree n :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨X.cyclic n x.1, by
          rw [f.mem_constantPreimageSubmodule_iff]
          have hx := (f.mem_constantPreimageSubmodule_iff P _ x.1).mp x.2
          rw [← ModuleCat.comp_apply, f.cyclic_naturality n,
            ModuleCat.comp_apply]
          change f.simplicial.app (.op (.mk n)) x.1 ∈ P
          exact hx⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }

@[simp]
theorem constantPreimageCyclic_coe
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) (n : ℕ)
    (x : (f.constantPreimageSimplicial P).degree n) :
    (f.constantPreimageCyclic P n x).1 = X.cyclic n x.1 :=
  rfl

theorem constantPreimageCyclic_iterate_coe
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) (n k : ℕ)
    (x : (f.constantPreimageSimplicial P).degree n) :
    (categoricalEndIterate (f.constantPreimageCyclic P n) k x).1 =
      categoricalEndIterate (X.cyclic n) k x.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [categoricalEndIterate_succ]
      change
        (f.constantPreimageCyclic P n
          (categoricalEndIterate (f.constantPreimageCyclic P n) k x)).1 =
        X.cyclic n (categoricalEndIterate (X.cyclic n) k x.1)
      rw [f.constantPreimageCyclic_coe, ih]

/-- Genuine cyclic submodule obtained by pulling back a submodule of constant coefficients. -/
def constantPreimage
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) : CyclicModule R where
  simplicial := f.constantPreimageSimplicial P
  cyclic := f.constantPreimageCyclic P
  cyclic_order n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change
      (categoricalEndIterate (f.constantPreimageCyclic P n) (n + 1) x).1 = x.1
    rw [f.constantPreimageCyclic_iterate_coe, X.cyclic_order]
    rfl
  cyclic_face_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (X.cyclic_face_zero n)) x.1
  cyclic_face_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (X.cyclic_face_succ n i)) x.1
  cyclic_degeneracy_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (X.cyclic_degeneracy_zero n)) x.1
  cyclic_degeneracy_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (X.cyclic_degeneracy_succ n i)) x.1

/-- Canonical inclusion of a constant-submodule inverse image into its ambient cyclic module. -/
def constantPreimageInclusion
    (f : CyclicModule.Hom X (moduleConstantCyclicModule (R := R) M))
    (P : Submodule R M) : CyclicModule.Hom (f.constantPreimage P) X where
  simplicial := f.constantPreimageSimplicialInclusion P
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

end CyclicModule.Hom
end RHTower
end GaloisForLFunctions
