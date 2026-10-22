import GaloisForLFunctions.RHTower.Deninger.DeningerTopThreeTermComplex
import Mathlib

/-!
# The complete locally convex ambient

Deninger's arithmetic coefficient takes values in complete Hausdorff locally convex spaces over the
reals, with continuous linear maps between them.  These form a category, and it is closed under
kernels: the kernel of a continuous linear map into a separated space is closed, a closed subspace
of a complete space is complete, and both local convexity and separation pass to subspaces.  So the
fibre of the arithmetic residue morphism stays in the complete locally convex world, with the
universal property of a kernel.

* `DeningerCLCS` : the category of complete Hausdorff locally convex real vector spaces.
* `DeningerCLCS.ker`, `DeningerCLCS.isLimitKer` : the fibre and its universal property.
* `DeningerCLCS.toTopModuleCat` : the forgetful functor to topological modules.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

/-- **A complete Hausdorff locally convex real vector space.** -/
structure DeningerCLCS where
  /-- The underlying type. -/
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℝ carrier]
  [uniformSpace : UniformSpace carrier]
  [isUniformAddGroup : IsUniformAddGroup carrier]
  [continuousSMul : ContinuousSMul ℝ carrier]
  [locallyConvex : LocallyConvexSpace ℝ carrier]
  [t2 : T2Space carrier]
  [complete : CompleteSpace carrier]

namespace DeningerCLCS

attribute [instance] addCommGroup module uniformSpace isUniformAddGroup continuousSMul
  locallyConvex t2 complete

instance : CoeSort DeningerCLCS Type := ⟨carrier⟩

/-- Build an object from an unbundled space. -/
abbrev of (M : Type) [AddCommGroup M] [Module ℝ M] [UniformSpace M] [IsUniformAddGroup M]
    [ContinuousSMul ℝ M] [LocallyConvexSpace ℝ M] [T2Space M] [CompleteSpace M] :
    DeningerCLCS := ⟨M⟩

/-- Morphisms are continuous linear maps. -/
structure Hom (X Y : DeningerCLCS) where
  /-- Build a morphism from a continuous linear map. -/
  ofHom' ::
  /-- The underlying continuous linear map. -/
  hom' : X →L[ℝ] Y

instance : Category DeningerCLCS where
  Hom := Hom
  id M := ⟨ContinuousLinearMap.id ℝ M⟩
  comp φ ψ := ⟨ψ.hom' ∘L φ.hom'⟩

instance : ConcreteCategory DeningerCLCS (· →L[ℝ] ·) where
  hom := Hom.hom'
  ofHom := Hom.ofHom'

/-- The continuous linear map underlying a morphism. -/
abbrev Hom.hom {X Y : DeningerCLCS} (f : X.Hom Y) : X →L[ℝ] Y :=
  ConcreteCategory.hom (C := DeningerCLCS) f

/-- The morphism attached to a continuous linear map. -/
abbrev ofHom {X Y : DeningerCLCS} (f : X →L[ℝ] Y) : X ⟶ Y :=
  ConcreteCategory.ofHom f

instance {X Y : DeningerCLCS} : Zero (X ⟶ Y) := ⟨ofHom 0⟩

instance : HasZeroMorphisms DeningerCLCS where
  comp_zero {X Y} f Z := by
    refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
    rfl
  zero_comp X {Y Z} g := by
    refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
    show (g.hom) 0 = 0
    exact map_zero _

section Kernel

variable {X Y : DeningerCLCS} (f : X ⟶ Y)

instance : IsClosed ((LinearMap.ker f.hom.toLinearMap : Submodule ℝ X) : Set X) :=
  ContinuousLinearMap.isClosed_ker f.hom

instance : IsUniformAddGroup (LinearMap.ker f.hom.toLinearMap) :=
  AddSubgroup.isUniformAddGroup (LinearMap.ker f.hom.toLinearMap).toAddSubgroup

/-- **The fibre of a continuous residue morphism**, as a complete locally convex space. -/
abbrev ker : DeningerCLCS := of (LinearMap.ker f.hom.toLinearMap)

/-- The inclusion of the fibre. -/
def kerι : ker f ⟶ X :=
  ofHom ⟨(LinearMap.ker f.hom.toLinearMap).subtype, continuous_subtype_val⟩

@[simp]
theorem kerι_apply (x : ker f) : (kerι f) x = x.1 := rfl

@[simp]
theorem kerι_comp : kerι f ≫ f = 0 := by
  refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
  exact x.2

/-- **The fibre has the universal property of the kernel.** -/
def isLimitKer : IsLimit (KernelFork.ofι (kerι f) (kerι_comp f)) :=
  isLimitAux (KernelFork.ofι (kerι f) (kerι_comp f))
    (fun s => ofHom ((Fork.ι s).hom.codRestrict (LinearMap.ker f.hom.toLinearMap) (fun m => by
      have hcond := KernelFork.condition s
      exact ConcreteCategory.congr_hom hcond m)))
    (fun s => by
      refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
      rfl)
    (fun s m hm => by
      refine ConcreteCategory.hom_ext_iff.2 (fun x => ?_)
      refine Subtype.ext ?_
      exact ConcreteCategory.congr_hom hm x)

end Kernel

/-- **The forgetful functor to topological modules**, which is where the three-term complex and its
homology live. -/
def toTopModuleCat : DeningerCLCS ⥤ TopModuleCat.{0} ℝ where
  obj X := TopModuleCat.of ℝ X.carrier
  map f := TopModuleCat.ofHom f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end DeningerCLCS

end RHTower
