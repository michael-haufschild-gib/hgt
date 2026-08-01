import GaloisForLFunctions.HTGeometry.DiscriminantPolynomial
import GaloisForLFunctions.HTGeometry.PolynomialNonSquare
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# The discriminant times the constant coefficient is not a square in the coefficient field

The elementary symmetric polynomials generate the symmetric subalgebra freely, so writing the
discriminant in them turns the coefficient ring into a polynomial ring in which the constant
coefficient of the generic polynomial is one of the variables.

The discriminant is not divisible by the top elementary symmetric function, so in those coordinates
it is not divisible by that variable, and multiplying by the variable produces an element whose
valuation at it is odd.  Such an element is not a square in the fraction field.

This is the square-class input of the even Kummer case: the two quadratic classes it compares are
the class of the discriminant and the class of the constant coefficient, and the statement is that
their product is nontrivial.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- **The fundamental theorem of symmetric polynomials as an isomorphism.**  Sending the `i`-th
variable to the `(i+1)`-st elementary symmetric function identifies a polynomial ring in `d`
variables with the symmetric subalgebra in `d` variables. -/
noncomputable def esymmAlgEquiv (K : Type*) [Field K] (d : ℕ) :
    MvPolynomial (Fin d) K ≃ₐ[K] MvPolynomial.symmetricSubalgebra (Fin d) K :=
  AlgEquiv.ofBijective (MvPolynomial.esymmAlgHom (Fin d) K d)
    (MvPolynomial.esymmAlgHom_fin_bijective K d)

theorem esymmAlgEquiv_apply_coe (p : MvPolynomial (Fin d) K) :
    ((esymmAlgEquiv K d p : MvPolynomial.symmetricSubalgebra (Fin d) K) :
      MvPolynomial (Fin d) K) =
      MvPolynomial.aeval (fun i : Fin d => MvPolynomial.esymm (Fin d) K (i + 1)) p :=
  MvPolynomial.esymmAlgHom_apply p

/-- The index of the variable carrying the top elementary symmetric function. -/
def topIndex (d : ℕ) (hd : 0 < d) : Fin d := ⟨d - 1, by omega⟩

/-- **The top variable carries the constant coefficient.** -/
theorem esymmAlgEquiv_X_topIndex (hd : 0 < d) :
    ((esymmAlgEquiv K d (MvPolynomial.X (topIndex d hd)) :
      MvPolynomial.symmetricSubalgebra (Fin d) K) : MvPolynomial (Fin d) K) =
      MvPolynomial.esymm (Fin d) K d := by
  rw [esymmAlgEquiv_apply_coe, MvPolynomial.aeval_X]
  congr 1
  simp only [topIndex, Fin.val_mk]
  omega

/-- The discriminant expressed in the elementary symmetric functions. -/
noncomputable def discCoeffPoly (K : Type*) [Field K] (d : ℕ) : MvPolynomial (Fin d) K :=
  (esymmAlgEquiv K d).symm
    ⟨vandermondePoly K d * vandermondePoly K d,
      MvPolynomial.mem_symmetricSubalgebra _ |>.2 isSymmetric_sq_vandermondePoly⟩

theorem esymmAlgEquiv_discCoeffPoly :
    ((esymmAlgEquiv K d (discCoeffPoly K d) :
      MvPolynomial.symmetricSubalgebra (Fin d) K) : MvPolynomial (Fin d) K) =
      vandermondePoly K d * vandermondePoly K d := by
  rw [discCoeffPoly, AlgEquiv.apply_symm_apply]

/-- **In symmetric coordinates the discriminant is not divisible by the constant coefficient.** -/
theorem topIndex_not_dvd_discCoeffPoly (hd : 0 < d) :
    ¬ (MvPolynomial.X (topIndex d hd) ∣ discCoeffPoly K d) := by
  rintro ⟨G, hG⟩
  refine esymm_top_not_dvd_sq_vandermondePoly (K := K) hd ?_
  refine ⟨((esymmAlgEquiv K d G : MvPolynomial.symmetricSubalgebra (Fin d) K) :
    MvPolynomial (Fin d) K), ?_⟩
  have h := congrArg
    (fun p : MvPolynomial (Fin d) K =>
      ((esymmAlgEquiv K d p : MvPolynomial.symmetricSubalgebra (Fin d) K) :
        MvPolynomial (Fin d) K)) hG
  simp only [map_mul, Subalgebra.coe_mul, esymmAlgEquiv_discCoeffPoly,
    esymmAlgEquiv_X_topIndex hd] at h
  exact h

/-- **The square class of the discriminant is not the square class of the constant coefficient.**
Their product has odd valuation at the variable carrying the constant coefficient, so it is not a
square in the coefficient field. -/
theorem not_isSquare_discCoeffPoly_mul_topIndex (hd : 0 < d) :
    ¬ IsSquare (algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))
      (discCoeffPoly K d * MvPolynomial.X (topIndex d hd))) :=
  not_isSquare_mul_X_of_not_dvd (topIndex_not_dvd_discCoeffPoly hd)

namespace SymmetricCoefficientNonSquare

/-- **The square-class input in the form the even Kummer case consumes it.**  The product of the
discriminant with the constant coefficient has no square root in the coefficient field. -/
theorem no_sqrt_discCoeffPoly_mul_topIndex {K : Type*} [Field K] {d : ℕ} (hd : 0 < d) :
    ¬ ∃ t : FractionRing (MvPolynomial (Fin d) K),
      algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))
          (discCoeffPoly K d) *
        algebraMap (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K))
          (MvPolynomial.X (topIndex d hd)) = t * t := by
  rintro ⟨t, ht⟩
  refine not_isSquare_discCoeffPoly_mul_topIndex (K := K) hd ⟨t, ?_⟩
  rw [map_mul]
  exact ht

end SymmetricCoefficientNonSquare

end GaloisForLFunctions.HTGeometry
