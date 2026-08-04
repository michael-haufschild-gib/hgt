import GaloisForLFunctions.HTGeometry.DifferentialLurothComponentTransfer

/-!
# The two-block splitting is differential

Splitting a doubled jet ring into a polynomial ring over the scalar jet ring turns the two-block
total derivative into the total derivative over the coefficient ring: the left block, which becomes
the coefficient ring, carries its own jet derivation, and the right block keeps its variables.

This is what lets a differential-ideal certificate be moved between the two views of a two-block
differential polynomial — the view in which the left block is a coefficient field and the view in
which the right block is.
-/

namespace GaloisForLFunctions

open MvPolynomial

open scoped Differential

noncomputable section

/-- The scalar differential-polynomial ring is itself a differential ring, by the jet derivation. -/
@[reducible] def differentialPolynomialDifferential (F : Type*) [CommRing F] [Differential F] :
    Differential (DifferentialPolynomial Unit F) :=
  ⟨differentialPolynomialOverDerivation Unit F⟩

/-- Iterated total derivative over an arbitrary differential coefficient ring. -/
def diffPolyIterate {ι K : Type*} [CommRing K] [Differential K] :
    ℕ → DifferentialPolynomial ι K → DifferentialPolynomial ι K
  | 0, P => P
  | n + 1, P => differentialPolynomialOverDerivation ι K (diffPolyIterate n P)

@[simp]
theorem diffPolyIterate_zero {ι K : Type*} [CommRing K] [Differential K]
    (P : DifferentialPolynomial ι K) : diffPolyIterate 0 P = P := rfl

@[simp]
theorem diffPolyIterate_succ {ι K : Type*} [CommRing K] [Differential K] (n : ℕ)
    (P : DifferentialPolynomial ι K) :
    diffPolyIterate (n + 1) P =
      differentialPolynomialOverDerivation ι K (diffPolyIterate n P) := rfl

/-- Over a field this is the corpus's iterated total derivative. -/
theorem diffPolyIterate_eq_familyIterateOver {ι K : Type*} [Field K] [Differential K] (n : ℕ)
    (P : DifferentialPolynomial ι K) :
    diffPolyIterate n P = differentialPolynomialFamilyIterateOver n P := by
  induction n with
  | zero => rfl
  | succ n hn => rw [diffPolyIterate_succ, differentialPolynomialFamilyIterateOver_succ, hn]

variable {F : Type*} [CommRing F] [Differential F]

/-- **The two-block splitting intertwines the two total derivations.**  On the right block the
variables are differentiated as variables; on the left block they are differentiated inside the
coefficient ring. -/
theorem differentialPolynomialTwoBlockEquiv_overDerivation
    (X : DifferentialPolynomial (Unit ⊕ Unit) F) :
    letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
    differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialOverDerivation (Unit ⊕ Unit) F X) =
      differentialPolynomialOverDerivation Unit (DifferentialPolynomial Unit F)
        (differentialPolynomialTwoBlockEquiv F X) := by
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  induction X using MvPolynomial.induction_on with
  | C c =>
      rw [differentialPolynomialOverDerivation_C, differentialPolynomialTwoBlockEquiv_C,
        differentialPolynomialTwoBlockEquiv_C]
      rw [differentialPolynomialOverDerivation_C]
      congr 1
      exact (differentialPolynomialOverDerivation_C c).symm
  | add P Q hP hQ =>
      rw [map_add, map_add, map_add, map_add, hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨u, n⟩
      cases u with
      | inl u =>
          obtain rfl : u = () := Subsingleton.elim _ _
          rw [Derivation.leibniz]
          simp only [smul_eq_mul, map_add, map_mul, hP,
            differentialPolynomialOverDerivation_X,
            differentialPolynomialTwoBlockEquiv_X_inl]
          rw [Derivation.leibniz]
          simp only [smul_eq_mul]
          have hc : (differentialPolynomialOverDerivation Unit (DifferentialPolynomial Unit F))
              (MvPolynomial.C (MvPolynomial.X ((), n))) =
              MvPolynomial.C (MvPolynomial.X ((), n + 1)) := by
            rw [differentialPolynomialOverDerivation_C]
            congr 1
            exact differentialPolynomialOverDerivation_X () n
          rw [hc]
      | inr u =>
          obtain rfl : u = () := Subsingleton.elim _ _
          rw [Derivation.leibniz]
          simp only [smul_eq_mul, map_add, map_mul, hP,
            differentialPolynomialOverDerivation_X,
            differentialPolynomialTwoBlockEquiv_X_inr]
          rw [Derivation.leibniz]
          simp only [smul_eq_mul, differentialPolynomialOverDerivation_X]

/-- The two-block splitting commutes with every iterated total derivative. -/
theorem differentialPolynomialTwoBlockEquiv_diffPolyIterate (n : ℕ)
    (X : DifferentialPolynomial (Unit ⊕ Unit) F) :
    letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
    differentialPolynomialTwoBlockEquiv F (diffPolyIterate n X) =
      diffPolyIterate n (differentialPolynomialTwoBlockEquiv F X) := by
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  induction n with
  | zero => rfl
  | succ n hn =>
      rw [diffPolyIterate_succ, diffPolyIterate_succ, ← hn,
        differentialPolynomialTwoBlockEquiv_overDerivation]

end

end GaloisForLFunctions
