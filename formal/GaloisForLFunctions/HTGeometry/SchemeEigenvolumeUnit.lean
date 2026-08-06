import GaloisForLFunctions.HTGeometry.SchemeEigenvolumeHorizon

/-!
# The eigenvolume condition on a scheme from an invariant coframe

Taking the top exterior power of an invariant space of rational one-forms multiplies the volume
form by the determinant of the transition matrix, which is an invertible constant.  A rational
function whose order of vanishing is zero everywhere does not move the divisor of another, so the
eigenvolume condition of the horizon theorem is a consequence of invariance of the coframe rather
than a hypothesis about orders.  An invertible section over an open set containing every point is
such a function.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **A nowhere vanishing rational function does not move divisors.** -/
theorem ord_mul_of_ord_eq_zero {c g : X.functionField} (hc0 : c ≠ 0) (hg : g ≠ 0)
    (hc : ∀ z : X, Scheme.ord c z = 0) (z : X) :
    Scheme.ord (c * g) z = Scheme.ord g z := by
  rw [Scheme.ord_mul hc0 hg, hc z, zero_add]

/-- An invertible section over an open set containing every point has order of vanishing zero
everywhere. -/
theorem ord_eq_zero_of_isUnit_section {U : X.Opens} [Nonempty U] {c : Γ(X, U)}
    (hc : IsUnit c) (hU : ∀ z : X, z ∈ U) (z : X) :
    Scheme.ord (X.germToFunctionField U c) z = 0 :=
  Scheme.ord_of_isUnit hc (hU z)

/-- **The eigenvolume condition from an invariant coframe.**  If the pullback of the volume form,
namely `Pg * J`, is a nowhere vanishing constant times the form itself, then it has the same
divisor as the form. -/
theorem schemeEigenvolume_condition_of_ord_eq_zero {c : X.functionField} (hc0 : c ≠ 0)
    (hc : ∀ z : X, Scheme.ord c z = 0) {g J Pg : X.functionField} (hg : g ≠ 0)
    (hid : Pg * J = c * g) (z : CodimOnePoint X) :
    Scheme.ord (Pg * J) z.1 = Scheme.ord g z.1 := by
  rw [hid]
  exact ord_mul_of_ord_eq_zero hc0 hg hc z.1

section UnitHorizon

variable (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ)
variable {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0) (hg : g ≠ 0)
variable (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
variable (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
variable {c : X.functionField} (hc0 : c ≠ 0) (hc : ∀ z : X, Scheme.ord c z = 0)
variable (hid : Pg * J = c * g)

include hPg hJ0 hg hpull hjac hc0 hc hid in
/-- **A self-morphism is unramified off the horizon of an invariant coframe.** -/
theorem unitSchemeEigenvolume_ramificationIndex_eq_one_off_horizon {z : CodimOnePoint X}
    (hz : ordAt g z = 0) : e z = 1 :=
  schemeEigenvolume_ramificationIndex_eq_one_off_horizon F e hPg hJ0 hpull hjac
    (schemeEigenvolume_condition_of_ord_eq_zero hc0 hc hg hid) hz

variable [CompactSpace X]
variable (hF : Function.Surjective F) (hone : ∀ z : CodimOnePoint X, 1 ≤ e z)
variable (hram : ∀ y : CodimOnePoint X, ordAt g y ≠ 0 → ∀ n : ℕ, 0 < n → F^[n] y = y →
  ∃ k < n, 1 < e (F^[k] y))

include hPg hJ0 hg hpull hjac hc0 hc hid hF hone hram in
/-- **The horizon of an invariant coframe is a reduced divisor.** -/
theorem unitSchemeEigenvolume_ordAt_eq_neg_one {z : CodimOnePoint X} (hz : ordAt g z ≠ 0) :
    ordAt g z = -1 :=
  schemeEigenvolume_ordAt_eq_neg_one F e hPg hJ0 hpull hjac
    (schemeEigenvolume_condition_of_ord_eq_zero hc0 hc hg hid) hF hone hram hz

include hPg hJ0 hg hpull hjac hc0 hc hid hF hone hram in
/-- **The horizon of an invariant coframe is totally invariant.** -/
theorem unitSchemeEigenvolume_ordAt_ne_zero_iff (z : CodimOnePoint X) :
    ordAt g z ≠ 0 ↔ ordAt g (F z) ≠ 0 :=
  schemeEigenvolume_ordAt_ne_zero_iff F e hPg hJ0 hpull hjac
    (schemeEigenvolume_condition_of_ord_eq_zero hc0 hc hg hid) hF hone hram z

end UnitHorizon

end GaloisForLFunctions.HTGeometry
