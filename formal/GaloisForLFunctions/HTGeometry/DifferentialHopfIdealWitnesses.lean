import GaloisForLFunctions.HTGeometry.DifferentialHopfIdeal

/-!
# Realizations of the additive differential Hopf-ideal interface

The zero ideal satisfies both coideal conditions, because the additive comultiplication is an
algebra map and the constant coefficient of zero vanishes.  This is the base point of the additive
unipotent Hopf-ideal lattice.
-/

namespace GaloisForLFunctions

/-- The zero ideal is an additive differential Hopf ideal. -/
theorem isAdditiveDifferentialHopfIdeal_bot {ι C : Type*} [Field C] :
    IsAdditiveDifferentialHopfIdeal (⊥ : Ideal (DifferentialPolynomial ι C)) := by
  refine ⟨?_, ?_⟩
  · intro P hP
    rw [Ideal.mem_bot] at hP
    subst hP
    rw [map_zero]
    exact Ideal.zero_mem _
  · intro P hP
    rw [Ideal.mem_bot] at hP
    subst hP
    exact map_zero _

end GaloisForLFunctions
