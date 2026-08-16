import Mathlib

/-!
# The cross-product synchronization identity

Two linear maps of three-space that intertwine the cross product from opposite sides,
`x × B y = (A x) × y`, are equal and scalar.  Evaluating the identity on the standard basis turns it
into a linear system whose only solutions are the common multiples of the identity.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- **The cross-product synchronization identity.**  If `x × B y = (A x) × y` for all `x, y`, then
`A` and `B` are the same scalar multiple of the identity. -/
theorem eq_smul_one_of_cross_sync (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ x y : Fin 3 → ℝ, crossProduct x (B *ᵥ y) = crossProduct (A *ᵥ x) y) :
    ∃ lam : ℝ, A = lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
      B = lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have c : ∀ i j k : Fin 3,
      crossProduct (fun t => if t = i then (1 : ℝ) else 0)
        (B *ᵥ fun t => if t = j then (1 : ℝ) else 0) k =
      crossProduct (A *ᵥ fun t => if t = i then (1 : ℝ) else 0)
        (fun t => if t = j then (1 : ℝ) else 0) k :=
    fun i j k => congrFun (h _ _) k
  have E000 := c 0 0 0
  have E001 := c 0 0 1
  have E002 := c 0 0 2
  have E010 := c 0 1 0
  have E011 := c 0 1 1
  have E012 := c 0 1 2
  have E020 := c 0 2 0
  have E021 := c 0 2 1
  have E022 := c 0 2 2
  have E100 := c 1 0 0
  have E101 := c 1 0 1
  have E102 := c 1 0 2
  have E110 := c 1 1 0
  have E111 := c 1 1 1
  have E112 := c 1 1 2
  have E120 := c 1 2 0
  have E121 := c 1 2 1
  have E122 := c 1 2 2
  have E200 := c 2 0 0
  have E201 := c 2 0 1
  have E202 := c 2 0 2
  have E210 := c 2 1 0
  have E211 := c 2 1 1
  have E212 := c 2 1 2
  have E220 := c 2 2 0
  have E221 := c 2 2 1
  have E222 := c 2 2 2
  simp [crossProduct, Matrix.mulVec, dotProduct] at E000 E001 E002 E010 E011 E012 E020 E021 E022 E100 E101 E102 E110 E111 E112 E120 E121 E122 E200 E201 E202 E210 E211 E212 E220 E221 E222
  have hfin : ∀ p : Fin 3, p = 0 ∨ p = 1 ∨ p = 2 := by decide
  refine ⟨A 0 0, ?_, ?_⟩ <;> ext p q <;>
    rcases hfin p with rfl | rfl | rfl <;> rcases hfin q with rfl | rfl | rfl <;>
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;>
    norm_num +decide <;>
    linarith

end GaloisForLFunctions.HTGeometry
