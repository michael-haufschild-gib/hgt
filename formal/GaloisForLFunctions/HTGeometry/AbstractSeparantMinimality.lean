import Mathlib.Algebra.Polynomial.Derivative

/-!
# Ritt's separant step for an arbitrary annihilation predicate

Among the nonzero polynomials satisfying a predicate there is one of minimal
degree, and if the predicate holds for no polynomial of degree zero then the
derivative of a degree-minimal one cannot satisfy the predicate: the derivative
is nonzero of strictly smaller degree.

This is the degree bookkeeping behind Ritt's separant step, isolated from any
particular notion of differential annihilation.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A nonzero polynomial of minimal degree satisfying a predicate. -/
theorem exists_minimal_natDegree {R : Type*} [Semiring R] {A : Polynomial R → Prop}
    (h : ∃ P : Polynomial R, P ≠ 0 ∧ A P) :
    ∃ P : Polynomial R, P ≠ 0 ∧ A P ∧
      ∀ Q : Polynomial R, Q ≠ 0 → A Q → P.natDegree ≤ Q.natDegree := by
  classical
  obtain ⟨P₀, hP₀, hA₀⟩ := h
  have hex : ∃ m : ℕ, ∃ P : Polynomial R, P ≠ 0 ∧ A P ∧ P.natDegree = m :=
    ⟨P₀.natDegree, P₀, hP₀, hA₀, rfl⟩
  obtain ⟨P, hP, hA, hdeg⟩ := Nat.find_spec hex
  refine ⟨P, hP, hA, fun Q hQ hAQ => ?_⟩
  rw [hdeg]
  exact Nat.find_le ⟨Q, hQ, hAQ, rfl⟩

/-- **The derivative of a degree-minimal polynomial fails the predicate.** -/
theorem derivative_not_pred_of_minimal {R : Type*} [Semiring R] [IsAddTorsionFree R]
    {A : Polynomial R → Prop} {P : Polynomial R} (hdeg : P.natDegree ≠ 0)
    (hmin : ∀ Q : Polynomial R, Q ≠ 0 → A Q → P.natDegree ≤ Q.natDegree) :
    ¬ A (Polynomial.derivative P) := by
  intro hAd
  have hd0 : Polynomial.derivative P ≠ 0 := fun h0 =>
    hdeg (Polynomial.derivative_eq_zero.mp h0)
  exact absurd (hmin _ hd0 hAd) (not_le.mpr (Polynomial.natDegree_derivative_lt hdeg))

/-- **Ritt's separant step.**  If the predicate holds for some nonzero
polynomial but for none of degree zero, it holds for a nonzero polynomial of
positive degree whose derivative fails it. -/
theorem exists_pred_with_separant {R : Type*} [Semiring R] [IsAddTorsionFree R]
    {A : Polynomial R → Prop} (h : ∃ P : Polynomial R, P ≠ 0 ∧ A P)
    (hpos : ∀ Q : Polynomial R, Q ≠ 0 → A Q → Q.natDegree ≠ 0) :
    ∃ P : Polynomial R, P ≠ 0 ∧ A P ∧ P.natDegree ≠ 0 ∧
      ¬ A (Polynomial.derivative P) := by
  obtain ⟨P, hP, hA, hmin⟩ := exists_minimal_natDegree h
  exact ⟨P, hP, hA, hpos P hP hA, derivative_not_pred_of_minimal (hpos P hP hA) hmin⟩

end GaloisForLFunctions.HTGeometry
