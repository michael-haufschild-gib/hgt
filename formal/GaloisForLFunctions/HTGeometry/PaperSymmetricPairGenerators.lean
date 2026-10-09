import GaloisForLFunctions.HTGeometry.PaperMonicLeadingSubstitution
import GaloisForLFunctions.HTGeometry.SymmetricSquareMatrix

/-!
# The native symmetric pair has three independent universal coefficients

For the two universal rows, the existing `symmetricPair` gives
`ac`, `ad + bc`, `bd`. Its leading monomials have distinct, recoverable
product exponents, over every commutative coefficient ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped BigOperators MonomialOrder

noncomputable section

variable (K : Type*) [CommRing K]

/-- The existing symmetric-pair construction applied to two universal rows. -/
def paperSymmetricPairGenerator : Fin 3 → MvPolynomial (Fin 4) K :=
  symmetricPair ![X 0, X 1] ![X 2, X 3]

/-- The universal coefficients are homogeneous quadratics. -/
theorem paperSymmetricPairGenerator_homogeneous (i : Fin 3) :
    (paperSymmetricPairGenerator K i).IsHomogeneous 2 := by
  fin_cases i
  · exact (isHomogeneous_X K 0).mul (isHomogeneous_X K 2)
  · exact ((isHomogeneous_X K 0).mul (isHomogeneous_X K 3)).add
      ((isHomogeneous_X K 1).mul (isHomogeneous_X K 2))
  · exact (isHomogeneous_X K 1).mul (isHomogeneous_X K 3)

/-- Leading exponents of the three native symmetric-pair coefficients. -/
def paperSymmetricPairLeadingExponent : Fin 3 → (Fin 4 →₀ ℕ) :=
  ![Finsupp.single 0 1 + Finsupp.single 2 1,
    Finsupp.single 0 1 + Finsupp.single 3 1,
    Finsupp.single 1 1 + Finsupp.single 3 1]

/-- The mixed correction is strictly lower than the leading mixed monomial. -/
theorem paperSymmetricPair_mixed_lt :
    (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) ≺[MonomialOrder.lex]
      (Finsupp.single 0 1 + Finsupp.single 3 1) := by
  change ∃ i : Fin 4, (∀ j, j < i →
    (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) j =
      (Finsupp.single 0 1 + Finsupp.single 3 1 : Fin 4 →₀ ℕ) j) ∧
    (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) i <
      (Finsupp.single 0 1 + Finsupp.single 3 1 : Fin 4 →₀ ℕ) i
  refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
  simp

/-- Exact monic leading terms of the native universal symmetric pair. -/
theorem paperSymmetricPairGenerator_leading [Nontrivial K] (i : Fin 3) :
    MonomialOrder.lex.degree (paperSymmetricPairGenerator K i) =
      paperSymmetricPairLeadingExponent i ∧
    MonomialOrder.lex.Monic (paperSymmetricPairGenerator K i) := by
  have hdeg (a b : Fin 4) :
      MonomialOrder.lex.degree (X a * X b : MvPolynomial (Fin 4) K) =
        Finsupp.single a 1 + Finsupp.single b 1 := by
    rw [MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero]
    · rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
    · rw [MonomialOrder.leadingCoeff_X, MonomialOrder.leadingCoeff_X, one_mul]
      exact one_ne_zero
  have hmonic (a b : Fin 4) : MonomialOrder.lex.Monic
      (X a * X b : MvPolynomial (Fin 4) K) :=
    MonomialOrder.monic_X.mul MonomialOrder.monic_X
  fin_cases i
  · exact ⟨hdeg 0 2, hmonic 0 2⟩
  · have hlt : MonomialOrder.lex.degree (X 1 * X 2 : MvPolynomial (Fin 4) K) ≺[MonomialOrder.lex]
        MonomialOrder.lex.degree (X 0 * X 3 : MvPolynomial (Fin 4) K) := by
      rw [hdeg, hdeg]
      exact paperSymmetricPair_mixed_lt
    exact ⟨(MonomialOrder.degree_add_of_lt hlt).trans (hdeg 0 3), (hmonic 0 3).add_of_lt hlt⟩
  · exact ⟨hdeg 1 3, hmonic 1 3⟩

/-- The product exponents can be read directly from three of the four target coordinates. -/
theorem paperSymmetricPair_leadingExponent [Nontrivial K] (d : Fin 3 →₀ ℕ) :
    paperMonicLeadingExponent MonomialOrder.lex (paperSymmetricPairGenerator K) d =
      Finsupp.single 0 (d 0 + d 1) + Finsupp.single 1 (d 2) +
        Finsupp.single 2 (d 0) + Finsupp.single 3 (d 1 + d 2) := by
  simp_rw [paperMonicLeadingExponent, (paperSymmetricPairGenerator_leading K _).1]
  rw [Finsupp.sum_fintype]
  · ext j
    fin_cases j <;> simp [paperSymmetricPairLeadingExponent, Fin.sum_univ_succ]
  · intro i
    simp

/-- Independent leading product exponents, with no coefficient-field assumption. -/
theorem paperSymmetricPair_leadingExponent_injective [Nontrivial K] :
    Function.Injective (paperMonicLeadingExponent MonomialOrder.lex (paperSymmetricPairGenerator K)) := by
  intro d e h
  have h0 : d 0 = e 0 := by
    simpa [paperSymmetricPair_leadingExponent] using congrArg (fun f => f 2) h
  have h2 : d 2 = e 2 := by
    simpa [paperSymmetricPair_leadingExponent] using congrArg (fun f => f 1) h
  have h01 : d 0 + d 1 = e 0 + e 1 := by
    simpa [paperSymmetricPair_leadingExponent] using congrArg (fun f => f 0) h
  rw [h0] at h01
  have h1 : d 1 = e 1 := Nat.add_left_cancel h01
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The three native universal symmetric-pair coefficients are polynomially
independent over every commutative coefficient ring. -/
theorem paperSymmetricPairSubstitution_injective :
    Function.Injective (aeval (R := K) (paperSymmetricPairGenerator K)) := by
  nontriviality K
  exact paperMonicSubstitution_injective MonomialOrder.lex (paperSymmetricPairGenerator K)
    (fun i => (paperSymmetricPairGenerator_leading K i).2)
    (paperSymmetricPair_leadingExponent_injective K)

end

end GaloisForLFunctions.HTGeometry
