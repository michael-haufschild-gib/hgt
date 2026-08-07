import GaloisForLFunctions.HTGeometry.CDGAModule
import GaloisForLFunctions.HTGeometry.CDGAUnital

/-!
# Restriction of scalars along a morphism of algebras

A morphism of commutative differential graded algebras makes the target a differential graded module
over the source: the action is the product with the image, associativity is multiplicativity of the
morphism followed by associativity of the product, and the Leibniz rule is the Leibniz rule of the
target together with the fact that the morphism commutes with the differentials.

This is what lets an algebra over a base algebra be regarded as a module over it — the datum a
relative tensor product is defined against.

* `HTGeometry.CDGAHom.restrictModule` : the induced module structure.
* `HTGeometry.CDGAHom.restrictModule_unital` : it is unital when the morphism preserves the unit.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {W : ℕ → Type v} [∀ n, AddCommGroup (W n)] [∀ n, Module R (W n)]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {C : CDGAStructure R W} {A : CDGAStructure R X}

/-- **The target of a morphism of algebras is a module over the source.** -/
def CDGAHom.restrictModule (f : CDGAHom C A) : CDGAModuleStructure C X where
  act h c x := A.mul h (f.toFun _ c) x
  d := A.d
  act_add_left h c c' x := by
    show A.mul h (f.toFun _ (c + c')) x = _
    rw [f.map_add, A.mul_add_left]
  act_add_right h c x x' := A.mul_add_right h _ x x'
  act_smul_left h r c x := by
    show A.mul h (f.toFun _ (r • c)) x = _
    rw [f.map_smul, A.mul_smul_left]
  act_smul_right h r c x := A.mul_smul_right h r _ x
  act_assoc h₁ h₂ h₃ h₄ c c' x := by
    show A.mul h₂ (f.toFun _ (C.mul h₁ c c')) x = _
    rw [f.map_mul h₁ c c', A.mul_assoc h₁ h₂ h₃ h₄]
  d_add := A.d_add
  d_smul := A.d_smul
  d_d := A.d_d
  d_act h c x := by
    show A.d _ (A.mul h (f.toFun _ c) x)
      = A.mul _ (f.toFun _ (C.d _ c)) x + ((-1 : R)) ^ _ • A.mul _ (f.toFun _ c) (A.d _ x)
    rw [A.d_mul h (f.toFun _ c) x, f.map_d]

@[simp] theorem CDGAHom.restrictModule_act (f : CDGAHom C A) {a b n : ℕ} (h : a + b = n)
    (c : W a) (x : X b) : f.restrictModule.act h c x = A.mul h (f.toFun a c) x := rfl

@[simp] theorem CDGAHom.restrictModule_d (f : CDGAHom C A) (n : ℕ) (x : X n) :
    f.restrictModule.d n x = A.d n x := rfl

/-- **Restriction of scalars is unital** when the morphism sends the unit to the unit. -/
theorem CDGAHom.restrictModule_unital {u : CDGAUnit C} {v : CDGAUnit A} (f : CDGAHom C A)
    (hf : f.toFun 0 u.one = v.one) : CDGAModuleUnital u f.restrictModule := by
  refine ⟨fun b x => ?_⟩
  show A.mul (Nat.zero_add b) (f.toFun 0 u.one) x = x
  rw [hf]
  exact v.one_mul b x

end GaloisForLFunctions.HTGeometry
