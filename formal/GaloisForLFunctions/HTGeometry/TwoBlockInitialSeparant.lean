import GaloisForLFunctions.HTGeometry.TwoBlockEquivDerivation

/-!
# Right-block initial and separant of a two-block polynomial

The two-block splitting reads a polynomial in two jet blocks as a polynomial in the right block over
the ring of the left block.  Partial differentiation in a right-block jet is the same operation on
both sides of that splitting, and the coefficients of the right-block initial are coefficients of the
polynomial itself.

Both facts are support statements in disguise: they say that the multiplier produced by a
right-block pseudo-division introduces no left-block jet that was not already present.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F : Type*} [CommRing F]

/-- Partial differentiation in a right-block jet commutes with the two-block splitting. -/
theorem differentialPolynomialTwoBlockEquiv_pderiv_inr (n : ℕ)
    (X : DifferentialPolynomial (Unit ⊕ Unit) F) :
    differentialPolynomialTwoBlockEquiv F
        (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), n) X) =
      MvPolynomial.pderiv (((), n) : Unit × ℕ)
        (differentialPolynomialTwoBlockEquiv F X) := by
  classical
  induction X using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨u, k⟩
      cases u with
      | inl u =>
          obtain rfl : u = () := Subsingleton.elim _ _
          have hne : ((Sum.inl () : Unit ⊕ Unit), k) ≠ ((Sum.inr () : Unit ⊕ Unit), n) := by
            simp
          rw [Derivation.leibniz]
          simp only [smul_eq_mul, map_add, map_mul, hP,
            differentialPolynomialTwoBlockEquiv_X_inl,
            MvPolynomial.pderiv_X_of_ne hne]
          rw [Derivation.leibniz]
          simp [smul_eq_mul]
      | inr u =>
          obtain rfl : u = () := Subsingleton.elim _ _
          rw [Derivation.leibniz]
          simp only [smul_eq_mul, map_add, map_mul, hP,
            differentialPolynomialTwoBlockEquiv_X_inr]
          rw [Derivation.leibniz]
          simp only [smul_eq_mul]
          by_cases hk : k = n
          · subst hk
            simp
          · have hne1 : ((Sum.inr () : Unit ⊕ Unit), k) ≠ ((Sum.inr () : Unit ⊕ Unit), n) := by
              simp [hk]
            have hne2 : (((), k) : Unit × ℕ) ≠ (((), n) : Unit × ℕ) := by
              simp [hk]
            rw [MvPolynomial.pderiv_X_of_ne hne1, MvPolynomial.pderiv_X_of_ne hne2]
            simp

end

end GaloisForLFunctions
