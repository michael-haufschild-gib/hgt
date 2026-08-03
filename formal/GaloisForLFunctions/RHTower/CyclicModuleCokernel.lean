import GaloisForLFunctions.RHTower.KRealCyclicModule

/-!
# Degreewise cokernels of Real cyclic modules

This file constructs the algebraic cokernel of a cyclic-module morphism without replacing the
cyclic object by an untyped vector-space quotient.  In degree `n` the object is the module
quotient by the range in degree `n`; every simplicial map descends by naturality, and the cyclic
generator descends by cyclic naturality.  All cyclic identities are proved on quotient
representatives.

For an equivariant morphism, the quotient in every degree also inherits its Real or
quaternionic structure, and that structure commutes with faces, degeneracies, and cyclic
rotation.  This is the exact algebraic categorical operation underlying the CCM relative cyclic
module.  Replacing ranges by their topological closures is a separate analytic layer.
-/

noncomputable section

open CategoryTheory

universe u v

namespace GaloisForLFunctions
namespace RHTower
namespace CyclicModule

variable {R : Type u} [CommRing R]

/-- Degreewise module cokernel of the simplicial part of a cyclic morphism. -/
def Hom.cokernelSimplicial {X Y : CyclicModule R} (f : Hom X Y) :
    PresentedSimplicialObject (ModuleCat.{v} R) where
  obj j := ModuleCat.of R
    (Y.simplicial.obj j ⧸ LinearMap.range (f.simplicial.app j).hom)
  map {j k} g := ModuleCat.ofHom <|
    (LinearMap.range (f.simplicial.app j).hom).mapQ
      (LinearMap.range (f.simplicial.app k).hom)
      (Y.simplicial.map g).hom (by
        intro y hy
        obtain ⟨x, rfl⟩ := hy
        refine ⟨X.simplicial.map g x, ?_⟩
        have h := f.simplicial.naturality g
        simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x)
  map_id j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.simplicial.app j).hom).mkQ_surjective q
    change
      (LinearMap.range (f.simplicial.app j).hom).mkQ
          (Y.simplicial.map (𝟙 j) y) =
        (LinearMap.range (f.simplicial.app j).hom).mkQ y
    rw [Y.simplicial.map_id]
    rfl
  map_comp {i j k} g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.simplicial.app i).hom).mkQ_surjective q
    change
      (LinearMap.range (f.simplicial.app k).hom).mkQ
          (Y.simplicial.map (g ≫ h) y) =
        (LinearMap.range (f.simplicial.app k).hom).mkQ
          (Y.simplicial.map h (Y.simplicial.map g y))
    rw [Y.simplicial.map_comp]
    rfl

/-- Natural quotient projection onto the degreewise simplicial cokernel. -/
def Hom.cokernelProjection {X Y : CyclicModule R} (f : Hom X Y) :
    Y.simplicial ⟶ f.cokernelSimplicial where
  app j := ModuleCat.ofHom
    (LinearMap.range (f.simplicial.app j).hom).mkQ
  naturality {j k} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl

/-- Cyclic generator induced on a degreewise cokernel. -/
def Hom.cokernelCyclic {X Y : CyclicModule R} (f : Hom X Y) (n : ℕ) :
    f.cokernelSimplicial.degree n ⟶ f.cokernelSimplicial.degree n :=
  ModuleCat.ofHom <|
    (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mapQ
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom)
      (Y.cyclic n).hom (by
        intro y hy
        obtain ⟨x, rfl⟩ := hy
        refine ⟨X.cyclic n x, ?_⟩
        have h := f.cyclic_naturality n
        simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x)

@[simp]
theorem Hom.cokernelCyclic_mkQ {X Y : CyclicModule R}
    (f : Hom X Y) (n : ℕ) (y : Y.simplicial.degree n) :
    f.cokernelCyclic n
        ((LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ y) =
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ
        (Y.cyclic n y) :=
  rfl

/-- Iterated cyclic rotation also descends representativewise. -/
theorem Hom.cokernelCyclic_iterate_mkQ {X Y : CyclicModule R}
    (f : Hom X Y) (n k : ℕ) (y : Y.simplicial.degree n) :
    categoricalEndIterate (f.cokernelCyclic n) k
        ((LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ y) =
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ
        (categoricalEndIterate (Y.cyclic n) k y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [categoricalEndIterate]
      change f.cokernelCyclic n
          (categoricalEndIterate (f.cokernelCyclic n) k
            ((LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ y)) = _
      rw [ih]
      rfl

@[simp]
theorem Hom.cokernelSimplicial_map_mkQ {X Y : CyclicModule R}
    (f : Hom X Y) {j k : SimplexCategoryGenRelᵒᵖ} (g : j ⟶ k)
    (y : Y.simplicial.obj j) :
    f.cokernelSimplicial.map g
        ((LinearMap.range (f.simplicial.app j).hom).mkQ y) =
      (LinearMap.range (f.simplicial.app k).hom).mkQ
        (Y.simplicial.map g y) :=
  rfl

/-- Algebraic cokernel in the category of cyclic modules. -/
def Hom.cokernel {X Y : CyclicModule R} (f : Hom X Y) : CyclicModule R where
  simplicial := f.cokernelSimplicial
  cyclic := f.cokernelCyclic
  cyclic_order n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ_surjective q
    change categoricalEndIterate (f.cokernelCyclic n) (n + 1)
        ((LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ y) = _
    rw [f.cokernelCyclic_iterate_mkQ, Y.cyclic_order]
    rfl
  cyclic_face_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.simplicial.app (.op (.mk (n + 1)))).hom).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_face_zero n)) y
    exact congrArg
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ hy
  cyclic_face_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.simplicial.app (.op (.mk (n + 1)))).hom).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_face_succ n i)) y
    exact congrArg
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ hy
  cyclic_degeneracy_zero n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_degeneracy_zero n)) y
    exact congrArg
      (LinearMap.range (f.simplicial.app (.op (.mk (n + 1)))).hom).mkQ hy
  cyclic_degeneracy_succ n i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.simplicial.app (.op (.mk n))).hom).mkQ_surjective q
    have hy := DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (Y.cyclic_degeneracy_succ n i)) y
    exact congrArg
      (LinearMap.range (f.simplicial.app (.op (.mk (n + 1)))).hom).mkQ hy

/-- Degree-`n` `K_R` morphism underlying an equivariant cyclic morphism. -/
def KRealHom.degree {odd : Bool} {X Y : CyclicModule ℂ}
    {KX : KReal odd X} {KY : KReal odd Y} (f : KRealHom KX KY) (n : ℕ) :
    KRealMorphism (KX.real n) (KY.real n) where
  map := (f.toHom.simplicial.app (.op (.mk n))).hom
  commutes := f.real_naturality n

/-- Real/quaternionic structure inherited by the algebraic cyclic cokernel. -/
def KRealHom.cokernelKReal {odd : Bool} {X Y : CyclicModule ℂ}
    {KX : KReal odd X} {KY : KReal odd Y} (f : KRealHom KX KY) :
    KReal odd f.toHom.cokernel where
  real n := KRealStructure.cokernel (KX.real n) (KY.real n) (f.degree n)
  face_naturality n i q := by
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.toHom.simplicial.app (.op (.mk (n + 1)))).hom).mkQ_surjective q
    change
      (LinearMap.range (f.toHom.simplicial.app (.op (.mk n))).hom).mkQ
          ((KY.real n).sigma (Y.simplicial.δ i y)) =
        (LinearMap.range (f.toHom.simplicial.app (.op (.mk n))).hom).mkQ
          (Y.simplicial.δ i ((KY.real (n + 1)).sigma y))
    rw [KY.face_naturality]
  degeneracy_naturality n i q := by
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.toHom.simplicial.app (.op (.mk n))).hom).mkQ_surjective q
    change
      (LinearMap.range (f.toHom.simplicial.app (.op (.mk (n + 1)))).hom).mkQ
          ((KY.real (n + 1)).sigma (Y.simplicial.σ i y)) =
        (LinearMap.range (f.toHom.simplicial.app (.op (.mk (n + 1)))).hom).mkQ
          (Y.simplicial.σ i ((KY.real n).sigma y))
    rw [KY.degeneracy_naturality]
  cyclic_naturality n q := by
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (f.toHom.simplicial.app (.op (.mk n))).hom).mkQ_surjective q
    change
      (LinearMap.range (f.toHom.simplicial.app (.op (.mk n))).hom).mkQ
          ((KY.real n).sigma (Y.cyclic n y)) =
        (LinearMap.range (f.toHom.simplicial.app (.op (.mk n))).hom).mkQ
          (Y.cyclic n ((KY.real n).sigma y))
    rw [KY.cyclic_naturality]

end CyclicModule
end RHTower
end GaloisForLFunctions
