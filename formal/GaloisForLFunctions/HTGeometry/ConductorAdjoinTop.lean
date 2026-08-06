import GaloisForLFunctions.HTGeometry.MonogenicOfDigitExpansion
import Mathlib.RingTheory.Conductor

/-!
# The conductor of a monogenic extension is everything

The conductor of an element is the set of scalars carrying the whole ring into the subalgebra it
generates.  When that subalgebra is already the whole ring the condition is vacuous, so the
conductor is the unit ideal.

Applied to a finite extension of discrete valuation rings with trivial residue extension, whose
uniformizer generates the extension, the conductor is the unit ideal.  That is the factor standing
between the derivative of a minimal polynomial and the different.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The conductor of a generator is the unit ideal.** -/
theorem conductor_eq_top_of_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} (h : Algebra.adjoin R ({x} : Set S) = ⊤) : conductor R x = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  show ∀ b : S, (1 : S) * b ∈ Algebra.adjoin R ({x} : Set S)
  intro b
  rw [h]
  trivial

section Valuation

open IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

/-- **The conductor of a uniformizer of a finite extension of discrete valuation rings with
trivial residue extension is the unit ideal.** -/
theorem conductor_eq_top_of_uniformizer [Module.Finite A B] {πA : A} (hπA : Irreducible πA)
    {x : B} (hx : addVal B x = 1) (e : ℕ)
    (hres : ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0)
    (hdvd : algebraMap A B πA ∣ x ^ e) :
    conductor A x = ⊤ :=
  conductor_eq_top_of_adjoin_eq_top (adjoin_singleton_eq_top hπA hx e hres hdvd)

end Valuation

end GaloisForLFunctions.HTGeometry
