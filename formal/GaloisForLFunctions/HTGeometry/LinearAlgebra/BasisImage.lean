import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Basis images under injective linear maps

An injective linear map carries a basis to a linearly independent family.
The proof transports a vanishing finite linear combination back to the domain.
-/

namespace GaloisForLFunctions.HTGeometry

/-- An injective linear map carries every basis to a linearly independent family. -/
theorem basisImage_linearIndependent {R M N ι : Type*}
    [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R M) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    LinearIndependent R (fun i => f (b i)) := by
  apply linearIndependent_iff.mpr
  intro l hl
  apply (linearIndependent_iff.mp b.linearIndependent) l
  apply hf
  rw [map_zero]
  exact (Finsupp.apply_linearCombination R f (fun i => b i) l).trans hl

#print axioms basisImage_linearIndependent
end GaloisForLFunctions.HTGeometry
