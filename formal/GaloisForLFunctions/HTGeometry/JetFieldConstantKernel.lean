import GaloisForLFunctions.HTGeometry.JetHypertranscendence

/-!
# Constants of the free differential rational field

In finite free differential rank, differentiation raises the jet order of every nonconstant
rational expression.  Consequently an element with zero derivative already belongs to the base
field.  This supplies the exact constant-field instance required by Picard--Vessiot torsor
classifications on canonical free differential fields and their derivation-closed subfields.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

open JetField

noncomputable section

variable {C ι : Type*} [Field C] [CharZero C] [Fintype ι]

/-- The constants of a finite-rank free differential rational field are exactly the base field. -/
theorem jetField_mem_range_algebraMap_of_deriv_eq_zero
    {u : JetField C ι} (hu : u′ = 0) :
    u ∈ (algebraMap C (JetField C ι)).range := by
  have hbot : u ∈ (⊥ : IntermediateField C (JetField C ι)) := by
    by_contra hnot
    exact deriv_notMem_bot_of_notMem_bot hnot
      (by rw [hu]; exact IntermediateField.zero_mem _)
  rw [IntermediateField.mem_bot] at hbot
  exact RingHom.mem_range.mpr hbot

/-- The canonical free differential rational field introduces no new differential constants. -/
instance jetFieldContainConstants : Differential.ContainConstants C (JetField C ι) where
  mem_range_of_deriv_eq_zero := jetField_mem_range_algebraMap_of_deriv_eq_zero

end

end GaloisForLFunctions.HTGeometry
