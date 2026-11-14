import GaloisForLFunctions.HTGeometry.Thermofield.FinitePurification

/-!
# The exact opposite-copy operator dictionary

Every finite-temperature Schmidt coefficient is nonzero. Consequently every
left action on the thermofield double has a unique right representative. This
representative is the Gibbs-weighted transpose; it reverses multiplication and
is involutive. Diagonal charges are fixed by the dictionary.

This makes the two-copy operator mechanism of Maldacena,
*Eternal black holes in Anti-de-Sitter*, arXiv:hep-th/0106112, explicit in the
finite Gibbs model. It is an algebraic statement about the chosen state.
-/

open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The state-dependent transpose implementing the opposite-copy action. -/
def mirror (β : ℝ) (E : α → ℝ) (A : Matrix α α ℂ) : Matrix α α ℂ :=
  fun a b => (Real.sqrt (finiteGibbsStateWeight β E a) : ℂ) /
    (Real.sqrt (finiteGibbsStateWeight β E b) : ℂ) * A b a

omit [DecidableEq α] in
private theorem sqrt_weight_ne_zero (β : ℝ) (E : α → ℝ) (a : α) :
    (Real.sqrt (finiteGibbsStateWeight β E a) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (finiteGibbsStateWeight_pos β E a)).ne'

/-- Every left action has the explicitly constructed right representative. -/
theorem left_eq_right_mirror (β : ℝ) (E : α → ℝ) (A : Matrix α α ℂ) :
    left A (amplitude β E) = right (mirror β E A) (amplitude β E) := by
  ext a b
  simp only [left, right, amplitude, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply, mirror]
  field_simp [sqrt_weight_ne_zero β E a] <;> ring

/-- Full Schmidt support makes the right action faithful. -/
theorem right_action_injective (β : ℝ) (E : α → ℝ) :
    Function.Injective (fun B : Matrix α α ℂ => right B (amplitude β E)) := by
  intro B C h
  ext a b
  have hab := congrArg (fun M : Matrix α α ℂ => M b a) h
  simp only [right, amplitude, Matrix.diagonal_mul, Matrix.transpose_apply] at hab
  exact mul_left_cancel₀ (sqrt_weight_ne_zero β E b) hab

/-- The opposite-copy representative is unique, not merely an existence witness. -/
theorem left_eq_right_iff (β : ℝ) (E : α → ℝ) (A B : Matrix α α ℂ) :
    left A (amplitude β E) = right B (amplitude β E) ↔ B = mirror β E A := by
  rw [left_eq_right_mirror]
  exact ⟨fun h => (right_action_injective β E h).symm, fun h => by rw [h]⟩

omit [DecidableEq α] in
/-- Exchanging the two copies twice recovers the original observable. -/
theorem mirror_mirror (β : ℝ) (E : α → ℝ) (A : Matrix α α ℂ) :
    mirror β E (mirror β E A) = A := by
  ext a b
  simp only [mirror]
  field_simp [sqrt_weight_ne_zero β E a, sqrt_weight_ne_zero β E b] <;> ring

omit [DecidableEq α] in
/-- The opposite algebra reverses the order of operator products. -/
theorem mirror_mul (β : ℝ) (E : α → ℝ) (A B : Matrix α α ℂ) :
    mirror β E (A * B) = mirror β E B * mirror β E A := by
  ext a b
  simp only [mirror, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  field_simp [sqrt_weight_ne_zero β E a, sqrt_weight_ne_zero β E b,
    sqrt_weight_ne_zero β E c] <;> ring

omit [DecidableEq α] [Nonempty α] in
theorem mirror_add (β : ℝ) (E : α → ℝ) (A B : Matrix α α ℂ) :
    mirror β E (A + B) = mirror β E A + mirror β E B := by
  ext a b
  simp only [mirror, Matrix.add_apply, mul_add]

/-- Every diagonal quantity has the same representative on both copies. -/
theorem mirror_diagonal (β : ℝ) (E : α → ℝ) (f : α → ℂ) :
    mirror β E (Matrix.diagonal f) = Matrix.diagonal f := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [mirror, Matrix.diagonal_apply_eq, div_self (sqrt_weight_ne_zero β E a),
      one_mul]
  · simp only [mirror, Matrix.diagonal_apply_ne f hab,
      Matrix.diagonal_apply_ne f (Ne.symm hab),
      mul_zero]

end

end GaloisForLFunctions.HTGeometry.Thermofield

#print axioms GaloisForLFunctions.HTGeometry.Thermofield.left_eq_right_mirror
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.right_action_injective
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.left_eq_right_iff
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.mirror_mirror
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.mirror_mul
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.mirror_add
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.mirror_diagonal
