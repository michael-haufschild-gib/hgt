import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionSpectrum
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Degree growth and the missing polynomial outputs of a connection

The all-real algebraic spectrum exposes a positive invariant: a nonconstant coefficient
forces every nonzero output to start at its own degree. This is the rigidity needed for
a canonical low-degree remainder and an exact description of the connection cokernel.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The concrete nonconstant coefficient sector of polynomial connections. -/
abbrev GomesNonconstantPolynomialCoefficient := {A : ℝ[X] // A.derivative ≠ 0}

/-- Every coefficient in this sector has strictly positive degree. -/
theorem gomesNonconstantPolynomialCoefficient_degree_pos (A : GomesNonconstantPolynomialCoefficient) :
    0 < A.val.natDegree :=
  Nat.pos_of_ne_zero ((derivative_ne_zero).mp A.property)

/-- Nonzero outputs have exactly the coefficient degree plus the input degree. -/
theorem gomesPolynomialFirstOrder_nonconstant_degree
    (A : GomesNonconstantPolynomialCoefficient) (B : {B : ℝ[X] // B ≠ 0}) :
    (gomesPolynomialFirstOrderOperator A.val B.val).natDegree = A.val.natDegree + B.val.natDegree := by
  have ha : A.val ≠ 0 := by
    intro h
    exact A.property (by rw [h, derivative_zero])
  have hd : B.val.derivative.natDegree < (A.val * B.val).natDegree := by
    rw [natDegree_mul ha B.property]
    have hle := (natDegree_derivative_le B.val).trans (Nat.sub_le B.val.natDegree 1)
    have hpos := gomesNonconstantPolynomialCoefficient_degree_pos A
    linarith
  unfold gomesPolynomialFirstOrderOperator
  rw [natDegree_sub_eq_right_of_natDegree_lt hd, natDegree_mul ha B.property]

/-- Below a positive coefficient degree, the natural-degree test includes the zero polynomial correctly. -/
theorem gomesPolynomial_below_coefficient_degree_iff
    (A : GomesNonconstantPolynomialCoefficient) (Q : ℝ[X]) :
    Q ∈ degreeLT ℝ A.val.natDegree ↔ Q.natDegree < A.val.natDegree := by
  by_cases hq : Q = 0
  · rw [hq, natDegree_zero]
    exact iff_of_true (Submodule.zero_mem _) (gomesNonconstantPolynomialCoefficient_degree_pos A)
  · rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt hq]

/-- The only connection output below the coefficient degree is the zero output from zero input. -/
theorem gomesPolynomialFirstOrder_low_degree_iff
    (A : GomesNonconstantPolynomialCoefficient) (B : ℝ[X]) :
    gomesPolynomialFirstOrderOperator A.val B ∈ degreeLT ℝ A.val.natDegree ↔ B = 0 := by
  rw [gomesPolynomial_below_coefficient_degree_iff]
  by_cases hb : B = 0
  · rw [hb]
    simp only [gomesPolynomialFirstOrderOperator, derivative_zero, mul_zero, sub_zero, natDegree_zero]
    exact iff_of_true (gomesNonconstantPolynomialCoefficient_degree_pos A) True.intro
  · rw [gomesPolynomialFirstOrder_nonconstant_degree A ⟨B, hb⟩]
    exact iff_of_false (by have := Nat.le_add_right A.val.natDegree B.natDegree; linarith) hb

/-- The low-degree polynomial sector intersects the connection range only at zero. -/
theorem gomesPolynomialFirstOrder_range_inf_low_degree
    (A : GomesNonconstantPolynomialCoefficient) :
    LinearMap.range (gomesPolynomialFirstOrderLinearMap A.val) ⊓ degreeLT ℝ A.val.natDegree = ⊥ := by
  apply le_antisymm
  · intro Q hQ
    rcases hQ.1 with ⟨B, rfl⟩
    have hb := (gomesPolynomialFirstOrder_low_degree_iff A B).mp hQ.2
    rw [hb]
    simp [gomesPolynomialFirstOrderLinearMap, gomesPolynomialFirstOrderOperator]
  · exact bot_le

end GaloisForLFunctions.HTGeometry
