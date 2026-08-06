import GaloisForLFunctions.HTGeometry.SchemeOrderPullbackLaw
import GaloisForLFunctions.HTGeometry.SchemeEigenvolumeHorizon

/-!
# The Jacobian hypothesis from a local valuation

The horizon theorem asks for the Jacobian factor to have order one less than the ramification index
at every codimension-one point.  The order of vanishing there is the additive valuation of the local
ring, so a valuation statement about a local generator of the different is exactly that hypothesis.

This is the wiring between the local theory of the different and the divisor-level statement of the
horizon theorem: no new mathematics, but it makes the dependency explicit.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order IsDiscreteValuationRing

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **A local generator of the different has order one less than the ramification index.** -/
theorem ord_eq_sub_one_of_addVal_eq {z : X} (hz : coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] {s : X.presheaf.stalk z} (hs : s ≠ 0) {e : ℕ}
    (h : addVal (X.presheaf.stalk z) s = ((e - 1 : ℕ) : ℕ∞)) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField s) z = ((e - 1 : ℕ) : ℤ) :=
  ord_algebraMap_stalk_eq_addVal hz hs h

/-- **The Jacobian hypothesis of the horizon theorem, supplied pointwise.**  If at every
codimension-one point the Jacobian factor is the image of a local element whose valuation is one
less than the ramification index there, then the hypothesis `hjac` holds. -/
theorem jacobian_order_of_addVal (e : CodimOnePoint X → ℕ) (J : X.functionField)
    (s : ∀ z : CodimOnePoint X, X.presheaf.stalk z.1)
    (hdvr : ∀ z : CodimOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk z.1))
    (hne : ∀ z : CodimOnePoint X, s z ≠ 0)
    (hJ : ∀ z : CodimOnePoint X, algebraMap (X.presheaf.stalk z.1) X.functionField (s z) = J)
    (hval : ∀ z : CodimOnePoint X,
      haveI := hdvr z
      addVal (X.presheaf.stalk z.1) (s z) = ((e z - 1 : ℕ) : ℕ∞))
    (hone : ∀ z : CodimOnePoint X, 1 ≤ e z) (z : CodimOnePoint X) :
    Scheme.ord J z.1 = (e z : ℤ) - 1 := by
  haveI := hdvr z
  have hord := ord_eq_sub_one_of_addVal_eq z.2 (hne z) (hval z)
  rw [hJ z] at hord
  rw [hord]
  have h1 : 1 ≤ e z := hone z
  push_cast [Nat.cast_sub h1]
  ring

end GaloisForLFunctions.HTGeometry
