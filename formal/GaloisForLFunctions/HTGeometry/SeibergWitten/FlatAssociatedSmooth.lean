import GaloisForLFunctions.HTGeometry.SeibergWitten.AssociatedBundles

/-!
# Flat compatibility of associated and smooth spinor bundles

The algebraic associated bundles over the trivial flat principal `Spinᶜ(4)` torsor have total
spaces `ℝ⁴ × ℂ²` and `ℝ⁴ × ℂ`.  This module identifies those total spaces, over the base, with the
actual smooth constant vector bundles used by `SmoothSpinCBundlePrelude`.  The determinant case
uses the squared `U(1)` character from `AssociatedBundles`, despite its underlying flat smooth line
being trivial.

This is a compatibility theorem for the flat torsor only.  It does not construct a nontrivial
global principal lift or integrate the pointwise Clifford representation to that group action.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Base-preserving identification of the algebraic and smooth flat positive spinor total spaces. -/
def flatPositiveAssociatedSmoothTotalEquiv :
    flatTrivialPositiveAssociatedSpinCBundle.totalSpace ≃
      Bundle.TotalSpace (Fin 2 → ℂ) flatPositiveSpinorBundle where
  toFun := fun p => ⟨p.1, p.2⟩
  invFun := fun p => (p.1, p.2)
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- The positive-spinor total-space identification commutes with projection to four-space. -/
theorem flatPositiveAssociatedSmoothTotalEquiv_projection (p) :
    (flatPositiveAssociatedSmoothTotalEquiv p).1 =
      flatTrivialPositiveAssociatedSpinCBundle.projection p :=
  rfl

/-- Base-preserving identification of the algebraic and smooth flat negative spinor total spaces. -/
def flatNegativeAssociatedSmoothTotalEquiv :
    flatTrivialNegativeAssociatedSpinCBundle.totalSpace ≃
      Bundle.TotalSpace (Fin 2 → ℂ) flatNegativeSpinorBundle where
  toFun := fun p => ⟨p.1, p.2⟩
  invFun := fun p => (p.1, p.2)
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- The negative-spinor total-space identification commutes with projection to four-space. -/
theorem flatNegativeAssociatedSmoothTotalEquiv_projection (p) :
    (flatNegativeAssociatedSmoothTotalEquiv p).1 =
      flatTrivialNegativeAssociatedSpinCBundle.projection p :=
  rfl

/-- Base-preserving identification of the determinant-associated and smooth flat line spaces. -/
def flatDeterminantAssociatedSmoothTotalEquiv :
    flatTrivialDeterminantAssociatedSpinCBundle.totalSpace ≃
      Bundle.TotalSpace ℂ flatDeterminantLineBundle where
  toFun := fun p => ⟨p.1, p.2⟩
  invFun := fun p => (p.1, p.2)
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- The determinant total-space identification commutes with projection to four-space. -/
theorem flatDeterminantAssociatedSmoothTotalEquiv_projection (p) :
    (flatDeterminantAssociatedSmoothTotalEquiv p).1 =
      flatTrivialDeterminantAssociatedSpinCBundle.projection p :=
  rfl

/-- All three flat algebraic associated spaces match their smooth vector-bundle carriers. -/
structure FlatSpinCAssociatedSmoothCompatibility where
  positiveTotalEquiv : flatTrivialPositiveAssociatedSpinCBundle.totalSpace ≃
    Bundle.TotalSpace (Fin 2 → ℂ) flatPositiveSpinorBundle
  negativeTotalEquiv : flatTrivialNegativeAssociatedSpinCBundle.totalSpace ≃
    Bundle.TotalSpace (Fin 2 → ℂ) flatNegativeSpinorBundle
  determinantTotalEquiv : flatTrivialDeterminantAssociatedSpinCBundle.totalSpace ≃
    Bundle.TotalSpace ℂ flatDeterminantLineBundle

/-- Closed compatibility datum for all flat `Spinᶜ` associated carriers. -/
def flatSpinCAssociatedSmoothCompatibility : FlatSpinCAssociatedSmoothCompatibility where
  positiveTotalEquiv := flatPositiveAssociatedSmoothTotalEquiv
  negativeTotalEquiv := flatNegativeAssociatedSmoothTotalEquiv
  determinantTotalEquiv := flatDeterminantAssociatedSmoothTotalEquiv

end GaloisForLFunctions.HTGeometry.SeibergWitten
