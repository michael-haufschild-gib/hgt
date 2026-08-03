import GaloisForLFunctions.RHTower.KRealCyclicModule

/-!
# Intersections of kernels in the category of cyclic modules

The reduced Connes--Consani--Marcolli source is the degreewise intersection of the kernels of two
cyclic morphisms.  This file constructs that intersection as a literal cyclic module.  Every face,
degeneracy, and cyclic rotation is restricted using naturality of the two morphisms; all cyclic
identities are inherited by subtype extensionality.
-/

noncomputable section

open CategoryTheory

universe u v

namespace GaloisForLFunctions
namespace RHTower
namespace CyclicModule

variable {R : Type u} [CommRing R]

/-- Degreewise intersection of the kernels of two cyclic morphisms. -/
def Hom.doubleKernelSubmodule {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (j : SimplexCategoryGenRelᵒᵖ) :
    Submodule R (X.simplicial.obj j) :=
  LinearMap.ker (f.simplicial.app j).hom ⊓
    LinearMap.ker (g.simplicial.app j).hom

@[simp]
theorem Hom.mem_doubleKernelSubmodule_iff {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (j : SimplexCategoryGenRelᵒᵖ)
    (x : X.simplicial.obj j) :
    x ∈ f.doubleKernelSubmodule g j ↔
      f.simplicial.app j x = 0 ∧ g.simplicial.app j x = 0 := by
  simp [Hom.doubleKernelSubmodule]

/-- Presented simplicial module carried by the degreewise double kernel. -/
def Hom.doubleKernelSimplicial {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) :
    PresentedSimplicialObject (ModuleCat.{v} R) where
  obj j := ModuleCat.of R (f.doubleKernelSubmodule g j)
  map {j k} h := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨X.simplicial.map h x.1, by
        have hx := (f.mem_doubleKernelSubmodule_iff g j x.1).mp x.2
        rw [f.mem_doubleKernelSubmodule_iff]
        constructor
        · rw [← ModuleCat.comp_apply, f.simplicial.naturality h,
            ModuleCat.comp_apply, hx.1, map_zero]
        · rw [← ModuleCat.comp_apply, g.simplicial.naturality h,
            ModuleCat.comp_apply, hx.2, map_zero]⟩
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

/-- Inclusion of the double-kernel simplicial module into its ambient cyclic module. -/
def Hom.doubleKernelSimplicialInclusion {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) :
    f.doubleKernelSimplicial g ⟶ X.simplicial where
  app j := ModuleCat.ofHom (f.doubleKernelSubmodule g j).subtype
  naturality {j k} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Cyclic generator restricted to the degreewise double kernel. -/
def Hom.doubleKernelCyclic {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (n : ℕ) :
    (f.doubleKernelSimplicial g).degree n ⟶
      (f.doubleKernelSimplicial g).degree n :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ⟨X.cyclic n x.1, by
        have hx := (f.mem_doubleKernelSubmodule_iff g _ x.1).mp x.2
        rw [f.mem_doubleKernelSubmodule_iff]
        constructor
        · rw [← ModuleCat.comp_apply, f.cyclic_naturality n,
            ModuleCat.comp_apply, hx.1, map_zero]
        · rw [← ModuleCat.comp_apply, g.cyclic_naturality n,
            ModuleCat.comp_apply, hx.2, map_zero]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }

@[simp]
theorem Hom.doubleKernelCyclic_coe {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (n : ℕ)
    (x : (f.doubleKernelSimplicial g).degree n) :
    (f.doubleKernelCyclic g n x).1 =
      X.cyclic n x.1 :=
  rfl

/-- Iterated restricted rotation agrees with ambient rotation after coercion. -/
theorem Hom.doubleKernelCyclic_iterate_coe {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) (n k : ℕ)
    (x : (f.doubleKernelSimplicial g).degree n) :
    (categoricalEndIterate (f.doubleKernelCyclic g n) k x).1 =
      categoricalEndIterate (X.cyclic n) k x.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [categoricalEndIterate_succ]
      change
        (f.doubleKernelCyclic g n
          (categoricalEndIterate (f.doubleKernelCyclic g n) k x)).1 =
        X.cyclic n (categoricalEndIterate (X.cyclic n) k x.1)
      rw [f.doubleKernelCyclic_coe, ih]

/-- Intersection of two cyclic kernels, as a genuine cyclic module. -/
def Hom.doubleKernel {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) : CyclicModule R where
  simplicial := f.doubleKernelSimplicial g
  cyclic := f.doubleKernelCyclic g
  cyclic_order n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change
      (categoricalEndIterate (f.doubleKernelCyclic g n) (n + 1) x).1 = x.1
    rw [f.doubleKernelCyclic_iterate_coe, X.cyclic_order]
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

/-- Canonical inclusion of the double-kernel cyclic module into the ambient source. -/
def Hom.doubleKernelInclusion {X Y Z : CyclicModule R}
    (f : Hom X Y) (g : Hom X Z) : Hom (f.doubleKernel g) X where
  simplicial := f.doubleKernelSimplicialInclusion g
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

end CyclicModule
end RHTower
end GaloisForLFunctions
