import GaloisForLFunctions.HTGeometry.PolynomialPseudoDivision
import GaloisForLFunctions.HTGeometry.DifferentialKernelCharacteristic

/-!
# Reduction in a singled-out variable

Singling out one variable of a multivariable polynomial ring is a ring equivalence onto the univariate
polynomial ring over the remaining variables.  Transporting pseudo-division through it reduces one
polynomial modulo another in that variable, at the cost of a power of the divisor's leading
coefficient in that variable — its *initial*.

This is the reduction step of differential algebra, stated where it actually lives: in the jet
variable that carries the leader.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K σ : Type*} [Field K]

/-- Singling out a variable is a ring equivalence. -/
def mvPolynomialEquivPolynomialAt (i : σ) :
    MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {j : σ // j ≠ i} K) := by
  classical
  exact (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe i).symm).trans
    (MvPolynomial.optionEquivLeft K {j : σ // j ≠ i})

@[simp]
theorem mvPolynomialEquivPolynomialAt_apply (i : σ) (P : MvPolynomial σ K) :
    mvPolynomialEquivPolynomialAt i P = mvPolynomialAsPolynomialAt i P := rfl

/-- **Reduction in a singled-out variable.**  A power of the divisor's leading coefficient in that
variable makes division with remainder possible, and the remainder has strictly smaller degree in
it. -/
theorem exists_pseudo_div_at (i : σ) {P : MvPolynomial σ K} (hP : P ≠ 0) (Q : MvPolynomial σ K) :
    ∃ (k : ℕ) (A S : MvPolynomial σ K),
      ((mvPolynomialAsPolynomialAt i P).leadingCoeff) ^ k •
          mvPolynomialAsPolynomialAt i Q
        = mvPolynomialAsPolynomialAt i A * mvPolynomialAsPolynomialAt i P
          + mvPolynomialAsPolynomialAt i S ∧
      (mvPolynomialAsPolynomialAt i S).degree < (mvPolynomialAsPolynomialAt i P).degree := by
  classical
  obtain ⟨k, Q', S', hQS, hS⟩ :=
    exists_pseudo_div (mvPolynomialAsPolynomialAt i P) (mvPolynomialAsPolynomialAt_ne_zero hP)
      (mvPolynomialAsPolynomialAt i Q)
  refine ⟨k, (mvPolynomialEquivPolynomialAt i).symm Q',
    (mvPolynomialEquivPolynomialAt i).symm S', ?_, ?_⟩
  · simp only [← mvPolynomialEquivPolynomialAt_apply, AlgEquiv.apply_symm_apply]
    exact hQS
  · simp only [← mvPolynomialEquivPolynomialAt_apply, AlgEquiv.apply_symm_apply]
    exact hS

/-- Polynomials in the remaining variables become the constants of the univariate view. -/
theorem mvPolynomialEquivPolynomialAt_rename_val (i : σ)
    (R : MvPolynomial {j : σ // j ≠ i} K) :
    mvPolynomialEquivPolynomialAt i (MvPolynomial.rename Subtype.val R) = Polynomial.C R := by
  classical
  have hext : ((mvPolynomialEquivPolynomialAt i).toAlgHom.comp
        (MvPolynomial.rename (Subtype.val : {j : σ // j ≠ i} → σ)))
      = (Polynomial.CAlgHom : MvPolynomial {j : σ // j ≠ i} K →ₐ[K] _) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    show mvPolynomialEquivPolynomialAt i
        (MvPolynomial.rename Subtype.val (MvPolynomial.X j)) = Polynomial.C (MvPolynomial.X j)
    rw [MvPolynomial.rename_X]
    show (MvPolynomial.optionEquivLeft K {j : σ // j ≠ i})
        (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm (MvPolynomial.X (j : σ)))
      = Polynomial.C (MvPolynomial.X j)
    rw [MvPolynomial.rename_X]
    have hj : (Equiv.optionSubtypeNe i).symm (j : σ) = some j := by
      apply (Equiv.optionSubtypeNe i).injective
      simp [j.2]
    rw [hj, MvPolynomial.optionEquivLeft_X_some]
  exact congrArg (fun f => f R) hext

/-- **Reduction modulo a polynomial in a singled-out variable, with its initial.** -/
theorem exists_initial_pseudo_div (i : σ) {P : MvPolynomial σ K} (hP : P ≠ 0)
    (Q : MvPolynomial σ K) :
    ∃ (k : ℕ) (A S : MvPolynomial σ K),
      mvPolynomialInitialAt i P ^ k * Q = A * P + S ∧
      (mvPolynomialAsPolynomialAt i S).degree < (mvPolynomialAsPolynomialAt i P).degree := by
  classical
  obtain ⟨k, A, S, hid, hS⟩ := exists_pseudo_div_at i hP Q
  refine ⟨k, A, S, ?_, hS⟩
  refine (mvPolynomialEquivPolynomialAt i).injective ?_
  rw [map_mul, map_pow, map_add, map_mul]
  rw [mvPolynomialInitialAt, mvPolynomialEquivPolynomialAt_rename_val]
  simp only [mvPolynomialEquivPolynomialAt_apply]
  rw [← Polynomial.C_pow, ← smul_eq_C_mul]
  exact hid

end

end GaloisForLFunctions.HTGeometry
