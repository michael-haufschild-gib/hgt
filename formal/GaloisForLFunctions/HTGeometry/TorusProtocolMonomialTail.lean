import GaloisForLFunctions.HTGeometry.TorusProtocol
import GaloisForLFunctions.HTGeometry.TorusInvariantMonomials

/-!
# The complete tail of a torus protocol

The phase tail of a torus isogeny protocol is the fixed field of the closed erased sector of the
scaling action, and the invariants of any set of rescalings are the velocity field with the
annihilating monomials adjoined.  Combining the two identifies the tail exactly: the persistent
sector consists of the Maurer--Cartan velocities together with the monomials of the position whose
exponent vector is annihilated by every erased scalar.

This is the position/velocity splitting for the split torus with no hypothesis on the protocol
beyond nonsingularity of its steps.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C] [IsAlgClosed C]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

omit [IsAlgClosed C] in
include hx hgen in
/-- **The fixed field of a deck group of rescalings.** -/
theorem fixedField_torusScaleRep_eq_torusInvariantMonomialField (hconst : ∀ c : C, c′ = 0)
    (S : Subgroup (Fin r → Cˣ)) :
    IntermediateField.fixedField (S.map (torusScaleRep hx hgen))
      = (torusInvariantMonomialField C x (S : Set (Fin r → Cˣ))).restrictScalars C := by
  refine SetLike.ext fun z ↦ ?_
  rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_restrictScalars]
  constructor
  · intro hfix
    exact (torusScale_invariant_iff_mem_torusInvariantMonomialField hx hgen hconst).mp
      fun u hu ↦ hfix _ ⟨u, hu, rfl⟩
  · rintro hz σ ⟨u, hu, rfl⟩
    exact (torusScale_invariant_iff_mem_torusInvariantMonomialField hx hgen hconst).mpr hz u hu

include hx hgen in
/-- **The complete phase tail of a torus protocol.**  It is the differential field of the velocity
coordinates with the monomials annihilating the erased sector adjoined. -/
theorem torusProtocol_nonautonomousTail_eq_torusInvariantMonomialField
    [TopologicalSpace (Fin r → Cˣ)] [IsTopologicalGroup (Fin r → Cˣ)]
    [DiscreteTopology (Fin r → Cˣ)]
    (hconst : ∀ c : C, c′ = 0)
    (m : ℕ → Matrix (Fin r) (Fin r) ℤ) (hm : ∀ j, (m j).det ≠ 0) (i : ℕ) :
    nonautonomousTail (torusProtocol hx hgen m hm) i
      = (torusInvariantMonomialField C x
          ((erasedClosure (torusProtocolGroup C m) i : Subgroup (Fin r → Cˣ)) :
            Set (Fin r → Cˣ))).restrictScalars C := by
  rw [torusProtocol_nonautonomousTail_eq_fixedField hx hgen m hm i]
  exact fixedField_torusScaleRep_eq_torusInvariantMonomialField hx hgen hconst _

end

end GaloisForLFunctions.HTGeometry
