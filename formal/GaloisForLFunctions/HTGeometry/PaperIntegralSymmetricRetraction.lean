import GaloisForLFunctions.HTGeometry.PaperIntegralSymmetricProjection
import GaloisForLFunctions.HTGeometry.PaperSplitIdealContraction
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# A coefficient-linear symmetric retraction over arbitrary commutative rings

The integral Vandermonde projection and the fundamental symmetric algebra
equivalence pay every splitting requirement of the source normal-coordinate
application, without a field or characteristic-zero restriction.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- Return root polynomials to elementary-symmetric coefficients without factorial denominators. -/
def paperIntegralSymmetricCoefficientRetraction :
    MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K :=
  (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).symm.toLinearMap.comp
    ((paperIntegralSymmetricProjection K n).codRestrict
      (symmetricSubalgebra (Fin n) K).toSubmodule
      (paperIntegralSymmetricProjection_isSymmetric K n))

/-- Substituting the returned coefficients recovers exactly the integral symmetric projection. -/
theorem paperIntegralSymmetricCoefficientRetraction_spec (p : MvPolynomial (Fin n) K) :
    aeval (fun i : Fin n => esymm (Fin n) K (i + 1))
      (paperIntegralSymmetricCoefficientRetraction K n p) =
        paperIntegralSymmetricProjection K n p := by
  rw [← esymmAlgHom_apply]
  exact congrArg Subtype.val
    ((MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).apply_symm_apply
      ⟨paperIntegralSymmetricProjection K n p, paperIntegralSymmetricProjection_isSymmetric K n p⟩)

/-- The integral retraction fixes the polynomial coefficient ring pointwise. -/
theorem paperIntegralSymmetricCoefficientRetraction_map (p : MvPolynomial (Fin n) K) :
    paperIntegralSymmetricCoefficientRetraction K n
      (aeval (fun i : Fin n => esymm (Fin n) K (i + 1)) p) = p := by
  apply (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).injective
  apply Subtype.ext
  simp only [MvPolynomial.esymmAlgEquiv_apply, esymmAlgHom_apply]
  rw [paperIntegralSymmetricCoefficientRetraction_spec]
  apply paperIntegralSymmetricProjection_fixed
  rw [← esymmAlgHom_apply]
  exact (esymmAlgHom (Fin n) K n p).property

/-- The integral retraction is linear over every polynomial in the symmetric generators. -/
theorem paperIntegralSymmetricCoefficientRetraction_mul (p q : MvPolynomial (Fin n) K) :
    paperIntegralSymmetricCoefficientRetraction K n
      (aeval (fun i : Fin n => esymm (Fin n) K (i + 1)) p * q) =
        p * paperIntegralSymmetricCoefficientRetraction K n q := by
  apply (MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n)).injective
  apply Subtype.ext
  simp only [MvPolynomial.esymmAlgEquiv_apply, esymmAlgHom_apply]
  rw [paperIntegralSymmetricCoefficientRetraction_spec,
    map_mul (aeval (R := K) (fun i : Fin n => esymm (Fin n) K (i + 1))) p
      (paperIntegralSymmetricCoefficientRetraction K n q),
    paperIntegralSymmetricCoefficientRetraction_spec]
  apply paperIntegralSymmetricProjection_mul
  rw [← esymmAlgHom_apply]
  exact (esymmAlgHom (Fin n) K n p).property

/-- Every coefficient-linear splitting requirement is proved over an arbitrary commutative ring. -/
def paperIntegralElementarySymmetricRetraction :
    PaperIdealRetraction
      (aeval (R := K) (fun i : Fin n => esymm (Fin n) K (i + 1))).toRingHom where
  retract := (paperIntegralSymmetricCoefficientRetraction K n).toAddMonoidHom
  retract_map := paperIntegralSymmetricCoefficientRetraction_map K n
  retract_mul := paperIntegralSymmetricCoefficientRetraction_mul K n

end

end GaloisForLFunctions.HTGeometry
