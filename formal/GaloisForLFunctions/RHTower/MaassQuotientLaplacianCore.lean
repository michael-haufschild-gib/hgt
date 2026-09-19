import GaloisForLFunctions.RHTower.MaassQuotientL2

/-!
# Maass quotient-Laplacian core identity

The current Maass source is an `L²` vector on its congruence quotient.  This
file connects its canonical quotient lift to the literal positive hyperbolic
Laplacian after restriction along the upper-half-plane section.  It is the core
eigen-equation required before a closed Friedrichs realization can extend the
source operator.
-/

namespace GaloisForLFunctions.RHTower

open UpperHalfPlane
open Matrix SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

/-- The quotient `L²` Maass source satisfies its literal hyperbolic Laplace
 equation after restriction along the canonical upper-half-plane section. -/
theorem MaassQuotientL2.sourceFunction_positiveHyperbolicLaplacian_section
    (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (z : ℍ) :
    positiveHyperbolicLaplacian
      (fun w : ℍ => sourceFunction N f (QuotientGroup.mk (UpperHalfPlane.toSL2R w)⁻¹)) z =
        (lam : ℂ) * sourceFunction N f (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹) := by
  have hsection : (fun w : ℍ =>
      sourceFunction N f (QuotientGroup.mk (UpperHalfPlane.toSL2R w)⁻¹)) = f.1.1 := by
    funext w
    exact maassInvariantQuotientLift_section _ _ w
  calc
    positiveHyperbolicLaplacian
        (fun w : ℍ => sourceFunction N f (QuotientGroup.mk (UpperHalfPlane.toSL2R w)⁻¹)) z =
        positiveHyperbolicLaplacian f.1.1 z := by rw [hsection]
    _ = (lam : ℂ) * f.1.1 z := f.2.2.1.2 z
    _ = (lam : ℂ) * sourceFunction N f
        (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹) := by
      rw [congrFun hsection z]

end

end GaloisForLFunctions.RHTower
