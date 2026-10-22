import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittOrientedSource

/-!
# Quotient form of the all-prime oriented Calderón--Witt endpoint

The finite-support all-prime oriented boundary has image exactly the global trace kernel.
Thus quotienting global degree-two source data by that image retains precisely its one-dimensional
orientation coefficient.
-/

namespace RHTower

/-- The all-prime oriented cokernel is canonically the complex orientation line. -/
noncomputable def deningerCalderonWittGlobalOrientedQuotientEquiv :
    ((DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) ⧸
      LinearMap.range deningerCalderonWittGlobalOrientedBoundary) ≃ₗ[ℂ] ℂ :=
  deningerCalderonWittGlobalOrientedBoundary_exact.linearEquivOfSurjective
    deningerCalderonWittGlobalOrientedTrace_surjective

/-- The quotient equivalence is represented by the global oriented trace. -/
theorem deningerCalderonWittGlobalOrientedQuotientEquiv_mk
    (z : DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) :
    deningerCalderonWittGlobalOrientedQuotientEquiv (Submodule.Quotient.mk z) =
      deningerCalderonWittGlobalOrientedTrace z :=
  rfl

end RHTower
