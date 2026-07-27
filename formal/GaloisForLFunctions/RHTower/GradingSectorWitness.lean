import GaloisForLFunctions.RHTower.KRealGradedAdjoint

/-!
# Both grading sectors are occupied

The graded-adjoint layer consumes `IsGradingEven γ a` together with `IsGradingOdd γ b`.  The corpus
proves the unit is even, but nothing exhibits an odd element, so the mixed statements — an even times
an odd is odd, the commutator of odds, and so on — were never applied to an actual odd element.

Both sectors have a clean criterion: conjugation by an involution fixes what commutes with it and
negates what anticommutes.  The sign grading on `2 × 2` matrices then occupies both sectors, with the
coordinate flip as an explicit nonzero odd element.

* **`isGradingEven_of_comm`**, **`isGradingOdd_of_anticomm`** — the criteria;
* **`signGrading_even_odd`** — both sectors occupied, the odd one nontrivially.
-/

namespace GaloisForLFunctions.RHTower

section Criteria

variable {A : Type*} [Ring A]

/-- An element commuting with the grading is even. -/
theorem isGradingEven_of_comm {γ a : A} (hγsq : γ * γ = 1) (h : γ * a = a * γ) :
    IsGradingEven γ a := by
  show γ * a * γ = a
  rw [h, mul_assoc, hγsq, mul_one]

/-- An element anticommuting with the grading is odd. -/
theorem isGradingOdd_of_anticomm {γ b : A} (hγsq : γ * γ = 1) (h : γ * b = -(b * γ)) :
    IsGradingOdd γ b := by
  show γ * b * γ = -b
  rw [h, neg_mul, mul_assoc, hγsq, mul_one]

end Criteria

/-! ### The sign grading on `2 × 2` matrices -/

/-- The diagonal sign involution. -/
def signGrading : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]

/-- The coordinate flip, which anticommutes with the sign involution. -/
def flipMatrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![0, 1], ![1, 0]]

theorem signGrading_sq : signGrading * signGrading = 1 := by
  rw [signGrading, Matrix.diagonal_mul_diagonal]
  have h : (fun i => ![(1 : ℝ), -1] i * ![(1 : ℝ), -1] i) = fun _ => (1 : ℝ) := by
    funext i
    fin_cases i <;> norm_num
  rw [h]
  exact Matrix.diagonal_one

theorem signGrading_anticomm : signGrading * flipMatrix = -(flipMatrix * signGrading) := by
  ext i j
  simp only [signGrading, Matrix.neg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> norm_num [flipMatrix]

theorem flipMatrix_ne_zero : flipMatrix ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [flipMatrix] at this

/-- **Both sectors are occupied.**  The sign involution has the unit as an even element and the
coordinate flip as a nonzero odd one. -/
theorem signGrading_even_odd :
    signGrading * signGrading = 1 ∧ IsGradingEven signGrading 1 ∧
      IsGradingOdd signGrading flipMatrix ∧ flipMatrix ≠ 0 :=
  ⟨signGrading_sq, isGradingEven_of_comm signGrading_sq (by rw [mul_one, one_mul]),
    isGradingOdd_of_anticomm signGrading_sq signGrading_anticomm, flipMatrix_ne_zero⟩

end GaloisForLFunctions.RHTower
