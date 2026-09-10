import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionDegreeInvariant

/-!
# Polynomial connection orbits

A nonconstant scalar connection raises every nonzero polynomial's degree by the
coefficient degree on each application. Its iterates therefore provide disjoint
chains from the low-degree monomials, preparing a complete linear normal form.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Nonconstant polynomial coefficients are nonzero. -/
theorem gomesNonconstantPolynomialCoefficient_ne_zero
    (A : GomesNonconstantPolynomialCoefficient) : A.val ≠ 0 := by
  intro h
  exact A.property (by rw [h, derivative_zero])

/-- Every connection iterate preserves the zero polynomial. -/
theorem gomesPolynomialFirstOrder_iterate_zero (A : ℝ[X]) (k : ℕ) :
    (gomesPolynomialFirstOrderOperator A)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [gomesPolynomialFirstOrderOperator, derivative_zero, mul_zero, sub_zero]

/-- Every iterate in the nonconstant sector is injective. -/
theorem gomesPolynomialFirstOrder_nonconstant_iterate_injective
    (A : GomesNonconstantPolynomialCoefficient) (k : ℕ) :
    Function.Injective ((gomesPolynomialFirstOrderOperator A.val)^[k]) :=
  ((gomesPolynomialFirstOrderOperator_injective_iff A.val).mpr
    (gomesNonconstantPolynomialCoefficient_ne_zero A)).iterate k

/-- A nonzero seed remains nonzero throughout its connection orbit. -/
theorem gomesPolynomialFirstOrder_nonconstant_iterate_ne_zero
    (A : GomesNonconstantPolynomialCoefficient) (Q : {Q : ℝ[X] // Q ≠ 0}) (k : ℕ) :
    (gomesPolynomialFirstOrderOperator A.val)^[k] Q.val ≠ 0 := by
  intro h
  apply Q.property
  apply gomesPolynomialFirstOrder_nonconstant_iterate_injective A k
  rw [h, gomesPolynomialFirstOrder_iterate_zero]

/-- Orbit degrees grow exactly linearly with the number of connection applications. -/
theorem gomesPolynomialFirstOrder_nonconstant_iterate_degree
    (A : GomesNonconstantPolynomialCoefficient) (Q : {Q : ℝ[X] // Q ≠ 0}) (k : ℕ) :
    ((gomesPolynomialFirstOrderOperator A.val)^[k] Q.val).natDegree =
      k * A.val.natDegree + Q.val.natDegree := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq, zero_mul, zero_add]
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      gomesPolynomialFirstOrder_nonconstant_degree A
        ⟨_, gomesPolynomialFirstOrder_nonconstant_iterate_ne_zero A Q k⟩,
      ih, Nat.succ_mul]
    ac_rfl

end GaloisForLFunctions.HTGeometry
