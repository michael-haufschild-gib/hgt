import GaloisForLFunctions.HTGeometry.SchemeEigenvolumeHorizon
import GaloisForLFunctions.HTGeometry.EigenvolumeBoundaryDivisor

/-!
# The boundary divisor of a scheme eigenvolume

On a scheme the horizon of an eigenvolume is a reduced divisor, so its boundary coefficient at
each codimension-one point is zero or one, and the ramification coefficient agrees with the
pullback difference of the boundary at every codimension-one point.  This is the coefficient form
of `R = f^* D - D`, which together with the pullback formula for the canonical class gives the
invariance of `K + D`.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

variable (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ)
variable {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0)
variable (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
variable (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
variable (heig : ∀ z : CodimOnePoint X, Scheme.ord (Pg * J) z.1 = Scheme.ord g z.1)
variable (hF : Function.Surjective F) (hone : ∀ z : CodimOnePoint X, 1 ≤ e z)
variable (hram : ∀ y : CodimOnePoint X, ordAt g y ≠ 0 → ∀ n : ℕ, 0 < n → F^[n] y = y →
  ∃ k < n, 1 < e (F^[k] y))

include hPg hJ0 hpull hjac heig hF hone hram in
/-- **The horizon of a scheme eigenvolume is a reduced divisor.**  The order of the eigenvolume at
a codimension-one point is zero or minus one. -/
theorem schemeEigenvolume_ordAt_eq_zero_or_neg_one (z : CodimOnePoint X) :
    ordAt g z = 0 ∨ ordAt g z = -1 :=
  order_eq_zero_or_neg_one hF hone
    (schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig)
    (finite_ordAt_support g) hram z

include hPg hJ0 hpull hjac heig hF hone hram in
/-- **The boundary coefficient of the horizon is zero or one.** -/
theorem schemeEigenvolume_boundaryCoeff_eq_zero_or_one (z : CodimOnePoint X) :
    boundaryCoeff (ordAt g) z = 0 ∨ boundaryCoeff (ordAt g) z = 1 :=
  boundaryCoeff_eq_zero_or_one hF hone
    (schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig)
    (finite_ordAt_support g) hram z

include hPg hJ0 hpull hjac heig hF hone hram in
/-- **Ramification is the pullback difference of the boundary at every codimension-one point.**
This is the coefficient form of `R = f^* D - D`. -/
theorem schemeEigenvolume_ramification_eq_pullback_sub (z : CodimOnePoint X) :
    (e z : ℤ) - 1 =
      (e z : ℤ) * boundaryCoeff (ordAt g) (F z) - boundaryCoeff (ordAt g) z :=
  ramification_eq_pullback_sub hF hone
    (schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig)
    (finite_ordAt_support g) hram z

end GaloisForLFunctions.HTGeometry
