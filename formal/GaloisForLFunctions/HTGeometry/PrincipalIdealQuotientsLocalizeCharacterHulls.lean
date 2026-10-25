import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Maps

/-!
# Principal ideal quotients localize character hulls

Away from the character zero set of the divisor, a principal ideal quotient
and the original ideal have the same vanishing characters.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

/-- A character nonzero at the divisor annihilates a principal ideal quotient
exactly when it annihilates the original ideal. -/
theorem principal_colon_le_character_ker_iff
    {A F : Type*} [CommRing A] [Field F] (I : Ideal A) (χ : A →+* F)
    (a : A) (ha : χ a ≠ 0) :
    I.colon (Ideal.span {a}) ≤ RingHom.ker χ ↔ I ≤ RingHom.ker χ := by
  constructor
  · exact fun h => Ideal.le_colon.trans h
  · intro h x hx
    have hprod := h (Ideal.mem_colon_span_singleton.mp hx)
    change χ (x * a) = 0 at hprod
    rw [map_mul] at hprod
    exact (mul_eq_zero.mp hprod).resolve_right ha

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.principal_colon_le_character_ker_iff
end
