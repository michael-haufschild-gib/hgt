import GaloisForLFunctions.HTGeometry.ConductorAdjoinTop
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Transporting a generator to the fraction field

A generator of a ring extension generates the corresponding extension of fraction fields.  The
image of the lower ring lands in the subalgebra generated over the lower fraction field, because
every element is a polynomial in the generator with coefficients from below; and that subalgebra is
a field when the generator is integral, so it contains the whole fraction field.

This is the hypothesis in the form the different ideal machinery expects, which states generation
over the fraction field rather than over the ring.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A B K L : Type*}
variable [CommRing A] [CommRing B] [Field K] [Field L]
variable [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/-- **The image of the ring lands in the subalgebra generated over the fraction field.** -/
theorem map_mem_adjoin_of_mem_adjoin {x : B} {b : B}
    (hb : b ∈ Algebra.adjoin A ({x} : Set B)) :
    algebraMap B L b ∈ Algebra.adjoin K ({algebraMap B L x} : Set L) := by
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  | algebraMap a =>
    rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
    exact Subalgebra.algebraMap_mem _ _
  | add p q _ _ hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul p q _ _ hp hq =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ hp hq

/-- The image of the whole ring lands in the subalgebra generated over the fraction field. -/
theorem range_le_adjoin_of_adjoin_eq_top {x : B}
    (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (b : B) :
    algebraMap B L b ∈ Algebra.adjoin K ({algebraMap B L x} : Set L) := by
  refine map_mem_adjoin_of_mem_adjoin (A := A) (K := K) ?_
  rw [hx]
  trivial

/-- **A generator of the ring generates the fraction field.**  The subalgebra generated over the
lower fraction field is a field, because the generator is algebraic there, and it contains the
image of the upper ring, hence its fraction field. -/
theorem adjoin_fraction_eq_top [IsFractionRing B L] {x : B}
    (halg : IsAlgebraic K (algebraMap B L x))
    (hx : Algebra.adjoin A ({x} : Set B) = ⊤) :
    Algebra.adjoin K ({algebraMap B L x} : Set L) = ⊤ := by
  have hsub := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg
  refine Algebra.eq_top_iff.mpr fun z => ?_
  rw [← hsub, IntermediateField.mem_toSubalgebra]
  obtain ⟨b, s, _, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  refine div_mem ?_ ?_
  · rw [← IntermediateField.mem_toSubalgebra, hsub]
    exact range_le_adjoin_of_adjoin_eq_top (A := A) hx b
  · rw [← IntermediateField.mem_toSubalgebra, hsub]
    exact range_le_adjoin_of_adjoin_eq_top (A := A) hx s

end GaloisForLFunctions.HTGeometry
