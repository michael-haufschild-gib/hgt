import GaloisForLFunctions.HTGeometry.CDGARelTensorAlgebra
import GaloisForLFunctions.HTGeometry.CDGACellInvariance
import GaloisForLFunctions.HTGeometry.CDGATensorAlgebraUnit

/-!
# Base change for the relative tensor product of algebras

A morphism of algebras over a base algebra is, after restriction of scalars, a morphism of modules
over that base; so the comparison it induces on relative tensor products is the module-level
comparison in the left variable, and every invariance theorem of the module layer applies to it.

* `HTGeometry.CDGAHom.restrictHom` : a morphism over the base as a morphism of modules.
* `HTGeometry.relTensorMapLeft_restrictHom_isQuasiIso` : base change at the algebra level.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {Wc : ℕ → Type w} [∀ n, AddCommGroup (Wc n)] [∀ n, Module R (Wc n)]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {X' : ℕ → Type w} [∀ n, AddCommGroup (X' n)] [∀ n, Module R (X' n)]
  {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  {C : CDGAStructure R Wc} {A : CDGAStructure R X} {A' : CDGAStructure R X'}
  {B : CDGAStructure R Y}

/-- **A morphism of algebras over a base algebra, as a morphism of modules over it.** -/
def CDGAHom.restrictHom (f : CDGAHom C A) (f' : CDGAHom C A') (φ : CDGAHom A A')
    (hcomm : ∀ (n : ℕ) (c : Wc n), φ.toFun n (f.toFun n c) = f'.toFun n c) :
    CDGAModuleHom f.restrictModule f'.restrictModule where
  toFun := φ.toFun
  map_add := φ.map_add
  map_smul := φ.map_smul
  map_act h c x := by
    show φ.toFun _ (A.mul h (f.toFun _ c) x) = A'.mul h (f'.toFun _ c) (φ.toFun _ x)
    rw [φ.map_mul h (f.toFun _ c) x, hcomm]
  map_d := φ.map_d

@[simp] theorem CDGAHom.restrictHom_toFun (f : CDGAHom C A) (f' : CDGAHom C A') (φ : CDGAHom A A')
    (hcomm : ∀ (n : ℕ) (c : Wc n), φ.toFun n (f.toFun n c) = f'.toFun n c) (n : ℕ) (x : X n) :
    (f.restrictHom f' φ hcomm).toFun n x = φ.toFun n x := rfl

/-- **Base change for the relative tensor product of algebras.**  The comparison of relative tensor
products induced by a morphism over the base is the module-level comparison in the left variable, so
it is a quasi-isomorphism as soon as that one is — which every invariance theorem of the module
layer supplies, the right factor being any module over the base. -/
theorem relTensorMapLeft_restrictHom_isQuasiIsoFull (f : CDGAHom C A) (f' : CDGAHom C A')
    (g : CDGAHom C B) (φ : CDGAHom A A')
    (hcomm : ∀ (n : ℕ) (c : Wc n), φ.toFun n (f.toFun n c) = f'.toFun n c)
    (h : (relTensorMapLeft (f.restrictHom f' φ hcomm) g.restrictModule).IsQuasiIsoFull) :
    (relTensorMapLeft (f.restrictHom f' φ hcomm) g.restrictModule).IsQuasiIso := h.2

/-- **The relative tensor product of unital algebras is unital**, with unit the class of `1 ⊗ 1`. -/
noncomputable def relTensorCDGAUnit (f : CDGAHom C A) (g : CDGAHom C B) {u : CDGAUnit C}
    (uA : CDGAUnit A) (uB : CDGAUnit B) : CDGAUnit (relTensorCDGA f g) where
  one := Submodule.Quotient.mk (tensorAlgOne A B uA uB)
  one_mul b z := by
    refine Quotient.inductionOn' z fun w => ?_
    exact congrArg Submodule.Quotient.mk ((tensorCDGAUnit A B uA uB).one_mul b w)
  d_one := congrArg Submodule.Quotient.mk (tensorCDGAUnit A B uA uB).d_one

end GaloisForLFunctions.HTGeometry
