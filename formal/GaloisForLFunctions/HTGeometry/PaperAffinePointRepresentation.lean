import GaloisForLFunctions.HTGeometry.AffineRationalPointSeparation
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.AmbientMaps

/-!
# Point coordinates for polynomial quotient presentations

The existing rational-point evaluation interface is an equivalence between
points of an affine zero locus and coefficient-algebra maps of its quotient.
Consequently, a polynomial-algebra presentation supplies actual point
coordinates, with the forward and inverse evaluations retained.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k] {σ τ : Type*}

/-- Coordinates of a rational point recovered from a quotient-algebra character. -/
def paperAffineCharacterCoordinates (I : Ideal (MvPolynomial σ k))
    (φ : (MvPolynomial σ k ⧸ I) →ₐ[k] k) : σ → k :=
  fun i => φ (Ideal.Quotient.mk I (X i))

/-- Polynomial evaluation at the recovered coordinates is the original character. -/
theorem paperAffineCharacterCoordinates_aeval (I : Ideal (MvPolynomial σ k))
    (φ : (MvPolynomial σ k ⧸ I) →ₐ[k] k) (p : MvPolynomial σ k) :
    aeval (paperAffineCharacterCoordinates I φ) p = φ (Ideal.Quotient.mk I p) :=
  AlgHom.congr_fun (aeval_unique (φ.comp (Ideal.Quotient.mkₐ k I))).symm p

/-- Every quotient-algebra character gives an actual zero-locus point. -/
def paperAffinePointOfCharacter (I : Ideal (MvPolynomial σ k))
    (φ : (MvPolynomial σ k ⧸ I) →ₐ[k] k) : AffineVarietyPoint I :=
  ⟨paperAffineCharacterCoordinates I φ, by
    apply mem_zeroLocus_iff.mpr
    intro p hp
    rw [paperAffineCharacterCoordinates_aeval, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]⟩

/-- Native rational-point evaluation is a full equivalence with algebra characters. -/
def paperAffinePointCharacterEquiv (I : Ideal (MvPolynomial σ k)) :
    AffineVarietyPoint I ≃ ((MvPolynomial σ k ⧸ I) →ₐ[k] k) where
  toFun := affineVarietyPointEvaluation I
  invFun := paperAffinePointOfCharacter I
  left_inv x := by
    apply Subtype.ext
    funext i
    change affineVarietyPointEvaluation I x (Ideal.Quotient.mk I (X i)) = x.val i
    rw [affineVarietyPointEvaluation_mk, aeval_X]
  right_inv φ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change affineVarietyPointEvaluation I (paperAffinePointOfCharacter I φ)
      (Ideal.Quotient.mk I (X i)) = φ (Ideal.Quotient.mk I (X i))
    rw [affineVarietyPointEvaluation_mk, aeval_X]
    rfl

/-- Polynomial-algebra characters are exactly their tuples of coordinate values. -/
def paperPolynomialCharacterPointEquiv : (MvPolynomial τ k →ₐ[k] k) ≃ (τ → k) where
  toFun φ := fun i => φ (X i)
  invFun x := aeval x
  left_inv φ := (aeval_unique φ).symm
  right_inv x := by funext i; exact aeval_X x i

/-- A polynomial presentation of an affine quotient induces actual affine point coordinates. -/
def paperAffinePointPolynomialEquiv (I : Ideal (MvPolynomial σ k))
    (e : (MvPolynomial σ k ⧸ I) ≃ₐ[k] MvPolynomial τ k) :
    AffineVarietyPoint I ≃ (τ → k) :=
  (paperAffinePointCharacterEquiv I).trans
    ((show ((MvPolynomial σ k ⧸ I) →ₐ[k] k) ≃ (MvPolynomial τ k →ₐ[k] k) from
      { toFun := fun φ => φ.comp e.symm.toAlgHom
        invFun := fun ψ => ψ.comp e.toAlgHom
        left_inv := by
          intro φ
          apply AlgHom.ext
          intro p
          change φ (e.symm (e p)) = φ p
          rw [e.symm_apply_apply]
        right_inv := by
          intro ψ
          apply AlgHom.ext
          intro p
          change ψ (e (e.symm p)) = ψ p
          rw [e.apply_symm_apply] }).trans paperPolynomialCharacterPointEquiv)

/-- Parametrization evaluates the displayed quotient generators in the polynomial presentation. -/
theorem paperAffinePointPolynomialEquiv_symm_apply (I : Ideal (MvPolynomial σ k))
    (e : (MvPolynomial σ k ⧸ I) ≃ₐ[k] MvPolynomial τ k) (y : τ → k) (i : σ) :
    ((paperAffinePointPolynomialEquiv I e).symm y).val i =
      aeval y (e (Ideal.Quotient.mk I (X i))) := rfl

/-- Inverse coordinates are evaluation of the inverse polynomial generators in the quotient. -/
theorem paperAffinePointPolynomialEquiv_apply (I : Ideal (MvPolynomial σ k))
    (e : (MvPolynomial σ k ⧸ I) ≃ₐ[k] MvPolynomial τ k)
    (x : AffineVarietyPoint I) (i : τ) :
    paperAffinePointPolynomialEquiv I e x i =
      affineVarietyPointEvaluation I x (e.symm (X i)) := rfl

end

end GaloisForLFunctions.HTGeometry
