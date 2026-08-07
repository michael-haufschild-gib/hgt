import GaloisForLFunctions.HTGeometry.CDGAUnital
import GaloisForLFunctions.HTGeometry.CDGATensorConst
import GaloisForLFunctions.HTGeometry.CDGAShift

/-!
# Cells are unital

Tensoring with a constant module and shifting both preserve the property that the unit of the
algebra acts as the identity, so a free cell over a unital algebra is a unital module.

* `HTGeometry.tensorConst_unital`, `HTGeometry.shift_unital`, `HTGeometry.freeCell_unital`.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- Tensoring with a constant module preserves unitality. -/
theorem tensorConst_unital {u : CDGAUnit A} {P : CDGAModuleStructure A M}
    (hP : CDGAModuleUnital u P) (V : Type w) [AddCommGroup V] [Module R V] :
    CDGAModuleUnital u (tensorConstModule P V) := by
  refine ⟨fun b z => ?_⟩
  show TensorProduct.map (P.actₗ (Nat.zero_add b) u.one) LinearMap.id z = z
  rw [show P.actₗ (Nat.zero_add b) u.one = LinearMap.id from
    LinearMap.ext fun m => hP.act_one b m, TensorProduct.map_id]
  rfl

/-- The degree shift preserves unitality. -/
theorem shift_unital {u : CDGAUnit A} {P : CDGAModuleStructure A M}
    (hP : CDGAModuleUnital u P) (k : ℕ) : CDGAModuleUnital u (shiftModule P k) := by
  refine ⟨fun b z => ?_⟩
  funext p
  obtain ⟨a, ha⟩ := p
  show shiftAct P k (Nat.zero_add b) u.one z ⟨a, ha⟩ = z ⟨a, ha⟩
  rw [shiftAct_apply_eq P k (Nat.zero_add b) u.one z (Nat.zero_add a) ha ha]
  exact hP.act_one a (z ⟨a, ha⟩)

/-- **A free cell is a unital module.** -/
theorem freeCell_unital (u : CDGAUnit A) (V : Type v) [AddCommGroup V] [Module R V] (k : ℕ) :
    CDGAModuleUnital u (freeCellModule A V k) :=
  shift_unital (tensorConst_unital (selfModule_unital u) V) k

end GaloisForLFunctions.HTGeometry
