import GaloisForLFunctions.HTGeometry.LogDerivativeSpanDichotomy

/-!
# An inner logarithmic derivative is removed by one conjugation

If the derivative of every member of a family of matrices is the commutator with one fixed matrix,
then conjugating by a solution of the corresponding linear system makes every member constant: the
three terms of the Leibniz expansion cancel identically, with no invertibility of the family needed.

This is the step that turns "the logarithmic derivative cocycle of a matrix group is a coboundary"
into "the group is constant after one conjugation" — the form in which a constant Galois group is
fed to the isomonodromy endgame.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C] {n : Type*} [Fintype n] [DecidableEq n]

/-- **An inner logarithmic derivative is removed by one conjugation.**  If the derivative of every
element of a set is the commutator with a fixed matrix, then conjugating by a solution of the
corresponding linear system makes every element constant. -/
theorem matrixDeriv_conjugate_eq_zero_of_commutator
    (A : Matrix n n C) (P : (Matrix n n C)ˣ)
    (hP : matrixDeriv (P : Matrix n n C) = A * (P : Matrix n n C))
    (M : Matrix n n C)
    (hM : matrixDeriv M = A * M - M * A) :
    matrixDeriv (((↑P⁻¹ : Matrix n n C)) * M * (P : Matrix n n C)) = 0 := by
  have hPinv : matrixDeriv ((↑P⁻¹ : Matrix n n C))
      = -(((↑P⁻¹ : Matrix n n C)) * A) := by
    have hcancel : (P : Matrix n n C) * ((↑P⁻¹ : Matrix n n C)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hcancel' : ((↑P⁻¹ : Matrix n n C)) * (P : Matrix n n C) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h0 : matrixDeriv (P : Matrix n n C) * ((↑P⁻¹ : Matrix n n C))
        + (P : Matrix n n C) * matrixDeriv ((↑P⁻¹ : Matrix n n C)) = 0 := by
      rw [← matrixDeriv_mul, hcancel, matrixDeriv_one]
    have h1 : (P : Matrix n n C) * matrixDeriv ((↑P⁻¹ : Matrix n n C))
        = -(A * (P : Matrix n n C) * ((↑P⁻¹ : Matrix n n C))) := by
      rw [eq_neg_iff_add_eq_zero, ← hP, add_comm]
      exact h0
    calc matrixDeriv ((↑P⁻¹ : Matrix n n C))
        = ((↑P⁻¹ : Matrix n n C)) * ((P : Matrix n n C)
            * matrixDeriv ((↑P⁻¹ : Matrix n n C))) := by
          rw [← mul_assoc, hcancel', one_mul]
      _ = ((↑P⁻¹ : Matrix n n C)) * (-(A * (P : Matrix n n C) * ((↑P⁻¹ : Matrix n n C)))) := by
          rw [h1]
      _ = -(((↑P⁻¹ : Matrix n n C)) * A) := by
          rw [mul_neg]
          congr 1
          rw [mul_assoc, hcancel, mul_one]
  rw [matrixDeriv_mul, matrixDeriv_mul, hPinv, hM, hP]
  noncomm_ring

/-- **A family whose logarithmic derivative is inner becomes constant after one conjugation.** -/
theorem forall_matrixDeriv_conjugate_eq_zero_of_commutator
    (G : Set (Matrix n n C)) (A : Matrix n n C) (P : (Matrix n n C)ˣ)
    (hP : matrixDeriv (P : Matrix n n C) = A * (P : Matrix n n C))
    (hG : ∀ M ∈ G, matrixDeriv M = A * M - M * A) :
    ∀ M ∈ G, matrixDeriv (((↑P⁻¹ : Matrix n n C)) * M * (P : Matrix n n C)) = 0 :=
  fun M hM => matrixDeriv_conjugate_eq_zero_of_commutator A P hP M (hG M hM)

/-- The inner cocycle condition, in logarithmic form: the logarithmic derivative of every element is
the difference of a fixed matrix and its conjugate. -/
theorem matrixDeriv_eq_commutator_of_unitLogDeriv (A : Matrix n n C) (M : (Matrix n n C)ˣ)
    (h : unitLogDeriv M = A - (M : Matrix n n C) * A * ((↑M⁻¹ : Matrix n n C))) :
    matrixDeriv (M : Matrix n n C) = A * (M : Matrix n n C) - (M : Matrix n n C) * A := by
  have hcancel : ((↑M⁻¹ : Matrix n n C)) * (M : Matrix n n C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hval : matrixDeriv (M : Matrix n n C) * ((↑M⁻¹ : Matrix n n C))
      = A - (M : Matrix n n C) * A * ((↑M⁻¹ : Matrix n n C)) := h
  calc matrixDeriv (M : Matrix n n C)
      = matrixDeriv (M : Matrix n n C) * (((↑M⁻¹ : Matrix n n C)) * (M : Matrix n n C)) := by
        rw [hcancel, mul_one]
    _ = (matrixDeriv (M : Matrix n n C) * ((↑M⁻¹ : Matrix n n C))) * (M : Matrix n n C) := by
        rw [mul_assoc]
    _ = (A - (M : Matrix n n C) * A * ((↑M⁻¹ : Matrix n n C))) * (M : Matrix n n C) := by
        rw [hval]
    _ = A * (M : Matrix n n C) - (M : Matrix n n C) * A := by
        rw [sub_mul, mul_assoc, mul_assoc, hcancel, mul_one]

end

end GaloisForLFunctions.HTGeometry
