import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# The ramification order law in the order-of-vanishing vocabulary

`Ring.ord` is the order of vanishing of an element of a Noetherian local ring, defined by module
length, and it is the primitive on which the scheme-level order of vanishing along a
codimension-one point is built.  For a discrete valuation ring it agrees with the additive
valuation.

This module restates the local ramification order law in that vocabulary, so that the law is
available at the interface used by the geometric order of vanishing rather than only in terms of
`IsDiscreteValuationRing.addVal`.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- **The ramification index scales the order of vanishing.** -/
theorem ord_map_eq_mul_ramification (φ : A →+* B) {π : A} (hπ : Irreducible π)
    (e : ℕ) (he : Ring.ord B (φ π) = (e : ℕ∞)) (a : A) (ha : a ≠ 0) :
    Ring.ord B (φ a) = (e : ℕ∞) * Ring.ord A a := by
  rw [Ring.ord_eq_addVal, Ring.ord_eq_addVal]
  refine addVal_map_eq_mul_ramification φ hπ e ?_ a ha
  rwa [Ring.ord_eq_addVal] at he

/-- **The local order law in the order-of-vanishing vocabulary.** -/
theorem ord_pullback_form (φ : A →+* B) {π : A} (hπ : Irreducible π)
    (e : ℕ) (he : Ring.ord B (φ π) = (e : ℕ∞)) (ω : A) (hω : ω ≠ 0)
    (jac : B) (hjac : Ring.ord B jac = ((e - 1 : ℕ) : ℕ∞)) :
    Ring.ord B (φ ω * jac) = (e : ℕ∞) * Ring.ord A ω + ((e - 1 : ℕ) : ℕ∞) := by
  rw [Ring.ord_eq_addVal, Ring.ord_eq_addVal]
  refine addVal_pullback_form φ hπ e ?_ ω hω jac ?_
  · rwa [Ring.ord_eq_addVal] at he
  · rwa [Ring.ord_eq_addVal] at hjac

/-- A uniformizer has order one. -/
theorem ord_uniformizer {π : A} (hπ : Irreducible π) : Ring.ord A π = 1 := by
  rw [Ring.ord_eq_addVal]
  exact addVal_uniformizer hπ

/-- Valuation zero characterises units. -/
theorem isUnit_of_addVal_eq_zero {x : B} (hx : addVal B x = 0) : IsUnit x := by
  have hle : addVal B x ≤ addVal B 1 := by
    rw [AddValuation.map_one, hx]
  exact isUnit_of_dvd_one (addVal_le_iff_dvd.mp hle)

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- **The ramification index of a local homomorphism is at least one.**  This is the hypothesis
`1 <= e` of the abstract ramification system, discharged. -/
theorem one_le_ord_map_uniformizer (φ : A →+* B)
    (hlocal : ∀ a : A, ¬ IsUnit a → ¬ IsUnit (φ a))
    {π : A} (hπ : Irreducible π) :
    1 ≤ Ring.ord B (φ π) := by
  rw [Ring.ord_eq_addVal]
  by_contra hcon
  have hzero : addVal B (φ π) = 0 := by
    have := not_le.mp hcon
    exact Order.lt_one_iff.mp this
  exact hlocal π hπ.not_isUnit (isUnit_of_addVal_eq_zero hzero)

end GaloisForLFunctions.HTGeometry
