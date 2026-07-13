import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.MvPolynomial.Equiv

namespace GaloisForLFunctions.HTGeometry

open scoped nonZeroDivisors

noncomputable section

theorem isRegular_of_ringEquiv
    {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) {r : R}
    (hr : IsRegular (e r)) : IsRegular r := by
  rw [isRegular_iff_eq_zero_of_mul] at hr ⊢
  constructor
  · intro x hx
    apply e.injective
    have hzero : e x = 0 := hr.1 (e x) (by simpa using congrArg e hx)
    simpa using hzero
  · intro x hx
    apply e.injective
    have hzero : e x = 0 := hr.2 (e x) (by simpa using congrArg e hx)
    simpa using hzero

/-- Multivariate McCoy certificate in finitely many variables: one coefficient that is a
non-zero-divisor makes the entire multivariate polynomial a non-zero-divisor. -/
theorem finMvPolynomial_mem_nonZeroDivisors_of_coeff_mem :
    ∀ (n : ℕ) {A : Type*} [CommRing A]
      (P : MvPolynomial (Fin n) A) (m : Fin n →₀ ℕ),
      P.coeff m ∈ nonZeroDivisors A → P ∈ nonZeroDivisors (MvPolynomial (Fin n) A) := by
  intro n
  induction n with
  | zero =>
      intro A _ P m hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      subst m
      rw [P.eq_C_of_isEmpty]
      let ord : MonomialOrder (Fin 0) := MonomialOrder.lex
      apply ord.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
      simpa using hm
  | succ n ih =>
      intro A _ P m hm
      let Q : Polynomial (MvPolynomial (Fin n) A) := MvPolynomial.finSuccEquiv A n P
      have hcoeff :
          (Q.coeff (m 0)).coeff m.tail ∈ nonZeroDivisors A := by
        dsimp [Q]
        rw [MvPolynomial.finSuccEquiv_coeff_coeff]
        simpa using hm
      have hQcoeff : Q.coeff (m 0) ∈ nonZeroDivisors (MvPolynomial (Fin n) A) :=
        ih (Q.coeff (m 0)) m.tail hcoeff
      have hQ : Q ∈ nonZeroDivisors (Polynomial (MvPolynomial (Fin n) A)) :=
        Polynomial.mem_nonzeroDivisors_of_coeff_mem (m 0) hQcoeff
      rw [← isRegular_iff_mem_nonZeroDivisors] at hQ ⊢
      exact isRegular_of_ringEquiv (MvPolynomial.finSuccEquiv A n).toRingEquiv hQ

end
end GaloisForLFunctions.HTGeometry
