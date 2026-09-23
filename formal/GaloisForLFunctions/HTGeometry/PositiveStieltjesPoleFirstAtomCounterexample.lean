import GaloisForLFunctions.HTGeometry.KreinLangerInertia

/-!
# Positive Stieltjes pole plus first atom counterexample

This module formalizes the exact rational degree-two counterexample from
`positive-stieltjes-pole-plus-first-atom-insufficient`.  On coefficient vectors
for real polynomials of degree at most two, it constructs the positive atomic
bulk on `0, 1, 2`, subtracts the pole atom at `-4`, and restores the first
trivial-zero atom at `-4/25`.  The pole form has exactly one negative square,
yet the repaired form is still negative on the constant polynomial.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- Coefficient vectors for real polynomials of degree at most two. -/
abbrev StieltjesCoeff := Fin 3 → ℝ

/-- Evaluation of a degree-two coefficient vector at a real point. -/
def stieltjesEval (z : ℝ) : StieltjesCoeff →ₗ[ℝ] ℝ where
  toFun := fun p => ∑ j, p j * z ^ (j : ℕ)
  map_add' := by
    intro p q
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a p
    change (∑ j, (a * p j) * z ^ (j : ℕ)) = a * ∑ j, p j * z ^ (j : ℕ)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The square of evaluation at one real atom. -/
def stieltjesAtom (z : ℝ) : QuadraticForm ℝ StieltjesCoeff :=
  (QuadraticMap.sq : QuadraticForm ℝ ℝ).comp (stieltjesEval z)

/-- The positive atomic Stieltjes bulk on `0`, `1`, and `2`. -/
def stieltjesBulk : QuadraticForm ℝ StieltjesCoeff :=
  (1 / 5 : ℝ) • stieltjesAtom 0 + (12 / 23 : ℝ) • stieltjesAtom 1 +
    (1 / 21 : ℝ) • stieltjesAtom 2

/-- The bulk after the pole-channel subtraction of mass four at `-4`. -/
def stieltjesPoleForm : QuadraticForm ℝ StieltjesCoeff :=
  stieltjesBulk - 4 • stieltjesAtom (-4)

/-- The pole form after adding the first-trivial-zero atom of mass `4/25`. -/
def stieltjesFirstAtomRepaired : QuadraticForm ℝ StieltjesCoeff :=
  stieltjesPoleForm + (4 / 25 : ℝ) • stieltjesAtom (-(4 / 25 : ℝ))

/-- The constant polynomial. -/
def stieltjesConstant : StieltjesCoeff := ![1, 0, 0]

/-- Twice the pole evaluation, whose square exactly cancels the pole subtraction. -/
def stieltjesPoleLinear : StieltjesCoeff →ₗ[ℝ] ℝ :=
  2 • stieltjesEval (-4)

/-- Pointwise nonnegativity is the semidefinite condition for the displayed real forms. -/
def stieltjesFormNonnegative (Q : QuadraticForm ℝ StieltjesCoeff) : Prop :=
  ∀ x, 0 ≤ Q x

@[simp] theorem stieltjesConstant_apply_zero : stieltjesConstant 0 = 1 := by rfl

@[simp] theorem stieltjesConstant_apply_one : stieltjesConstant 1 = 0 := by rfl

@[simp] theorem stieltjesConstant_apply_two : stieltjesConstant 2 = 0 := by rfl

theorem stieltjesEval_zero (p : StieltjesCoeff) : stieltjesEval 0 p = p 0 := by
  simp [stieltjesEval, Fin.sum_univ_succ]

theorem stieltjesEval_one (p : StieltjesCoeff) :
    stieltjesEval 1 p = p 0 + p 1 + p 2 := by
  simp [stieltjesEval, Fin.sum_univ_succ]
  ring

theorem stieltjesEval_two (p : StieltjesCoeff) :
    stieltjesEval 2 p = p 0 + 2 * p 1 + 4 * p 2 := by
  simp [stieltjesEval, Fin.sum_univ_succ]
  ring

theorem stieltjesBulk_apply (p : StieltjesCoeff) :
    stieltjesBulk p =
      (1 / 5 : ℝ) * (stieltjesEval 0 p) ^ (2 : ℕ) +
        (12 / 23 : ℝ) * (stieltjesEval 1 p) ^ (2 : ℕ) +
          (1 / 21 : ℝ) * (stieltjesEval 2 p) ^ (2 : ℕ) := by
  simp [stieltjesBulk, stieltjesAtom, QuadraticMap.sq_apply]
  ring

theorem stieltjesBulk_nonnegative (p : StieltjesCoeff) : 0 ≤ stieltjesBulk p := by
  rw [stieltjesBulk_apply]
  positivity

/-- The three positive atom evaluations separate nonzero degree-two polynomials. -/
theorem stieltjesBulk_posDef : stieltjesBulk.PosDef := by
  intro p hp
  rw [stieltjesBulk_apply]
  have h0nonneg : 0 ≤ (1 / 5 : ℝ) * (stieltjesEval 0 p) ^ (2 : ℕ) := by positivity
  have h1nonneg : 0 ≤ (12 / 23 : ℝ) * (stieltjesEval 1 p) ^ (2 : ℕ) := by positivity
  have h2nonneg : 0 ≤ (1 / 21 : ℝ) * (stieltjesEval 2 p) ^ (2 : ℕ) := by positivity
  by_cases h0 : stieltjesEval 0 p = 0
  · by_cases h1 : stieltjesEval 1 p = 0
    · by_cases h2 : stieltjesEval 2 p = 0
      · exfalso
        have hp0 : p 0 = 0 := by rwa [stieltjesEval_zero] at h0
        have hp1eq : p 0 + p 1 + p 2 = 0 := by rwa [stieltjesEval_one] at h1
        have hp2eq : p 0 + 2 * p 1 + 4 * p 2 = 0 := by
          rwa [stieltjesEval_two] at h2
        have hp1 : p 1 = 0 := by nlinarith
        have hp2 : p 2 = 0 := by nlinarith
        apply hp
        funext j
        fin_cases j <;> simp [hp0, hp1, hp2]
      · have h2pos : 0 < (1 / 21 : ℝ) * (stieltjesEval 2 p) ^ (2 : ℕ) := by
          exact mul_pos (by norm_num) (sq_pos_of_ne_zero h2)
        nlinarith
    · have h1pos : 0 < (12 / 23 : ℝ) * (stieltjesEval 1 p) ^ (2 : ℕ) := by
        exact mul_pos (by norm_num) (sq_pos_of_ne_zero h1)
      nlinarith
  · have h0pos : 0 < (1 / 5 : ℝ) * (stieltjesEval 0 p) ^ (2 : ℕ) := by
      exact mul_pos (by norm_num) (sq_pos_of_ne_zero h0)
    nlinarith

/-- Restoring the removed pole square is exactly the positive Stieltjes bulk. -/
theorem stieltjesPoleForm_add_square_eq_bulk (p : StieltjesCoeff) :
    stieltjesPoleForm p + (stieltjesPoleLinear p) ^ (2 : ℕ) = stieltjesBulk p := by
  simp [stieltjesPoleForm, stieltjesAtom, stieltjesPoleLinear, QuadraticMap.sq_apply]
  ring

theorem stieltjesConstant_ne_zero : stieltjesConstant ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  norm_num [stieltjesConstant] at h0

theorem stieltjesPoleForm_constant :
    stieltjesPoleForm stieltjesConstant = (-7802 / 2415 : ℝ) := by
  norm_num [stieltjesPoleForm, stieltjesBulk, stieltjesAtom, stieltjesEval,
    QuadraticMap.sq_apply, Fin.sum_univ_succ]

theorem stieltjesBulk_constant :
    stieltjesBulk stieltjesConstant = (1858 / 2415 : ℝ) := by
  norm_num [stieltjesBulk, stieltjesAtom, stieltjesEval, QuadraticMap.sq_apply,
    Fin.sum_univ_succ]

theorem stieltjesFirstAtomRepaired_constant :
    stieltjesFirstAtomRepaired stieltjesConstant = (-37078 / 12075 : ℝ) := by
  norm_num [stieltjesFirstAtomRepaired, stieltjesPoleForm, stieltjesBulk,
    stieltjesAtom, stieltjesEval, QuadraticMap.sq_apply,
    Fin.sum_univ_succ]

/-- The pole subtraction has exactly one negative square. -/
theorem stieltjesPoleForm_sigNeg_eq_one : sigNeg stieltjesPoleForm = 1 := by
  have hupper : sigNeg stieltjesPoleForm ≤ 1 :=
    sigNeg_le_one_of_add_sq_nonneg stieltjesPoleForm stieltjesPoleLinear
      (fun p => by
        rw [stieltjesPoleForm_add_square_eq_bulk]
        exact stieltjesBulk_nonnegative p)
  have hneg : stieltjesPoleForm stieltjesConstant < 0 := by
    rw [stieltjesPoleForm_constant]
    norm_num
  have hlower : 0 < sigNeg stieltjesPoleForm :=
    sigNeg_pos_of_exists_negativeVector stieltjesPoleForm stieltjesConstant_ne_zero hneg
  omega

/-- The first-trivial-zero atom does not repair the explicit pole deficit. -/
theorem stieltjesFirstAtomRepaired_not_nonnegative :
    ¬ stieltjesFormNonnegative stieltjesFirstAtomRepaired := by
  intro h
  have hconstant := h stieltjesConstant
  rw [stieltjesFirstAtomRepaired_constant] at hconstant
  norm_num at hconstant

theorem stieltjesBoundaryOrder :
    (-4 : ℝ) < -(4 / 25 : ℝ) ∧ -(4 / 25 : ℝ) < 0 := by
  norm_num

/-- Complete exact finite countermodel to pole-plus-first-atom repair. -/
theorem positiveStieltjesPolePlusFirstAtomInsufficient :
    stieltjesBulk.PosDef ∧
      sigNeg stieltjesPoleForm = 1 ∧
        ¬ stieltjesFormNonnegative stieltjesFirstAtomRepaired ∧
          stieltjesBulk stieltjesConstant = (1858 / 2415 : ℝ) ∧
            stieltjesPoleForm stieltjesConstant = (-7802 / 2415 : ℝ) ∧
              stieltjesFirstAtomRepaired stieltjesConstant = (-37078 / 12075 : ℝ) ∧
                (-4 : ℝ) < -(4 / 25 : ℝ) ∧ -(4 / 25 : ℝ) < 0 := by
  exact ⟨stieltjesBulk_posDef, stieltjesPoleForm_sigNeg_eq_one,
    stieltjesFirstAtomRepaired_not_nonnegative, stieltjesBulk_constant,
    stieltjesPoleForm_constant, stieltjesFirstAtomRepaired_constant,
    stieltjesBoundaryOrder.1, stieltjesBoundaryOrder.2⟩

end

end GaloisForLFunctions
