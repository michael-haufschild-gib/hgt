import GaloisForLFunctions.HTGeometry.FiniteAlgebraicStateBoundary
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicTransitivity
import GaloisForLFunctions.HTGeometry.LurothSaturationWitnesses

/-!
# Differentially algebraic observables are finite algebraic states

The state-elimination interface asks for a derivation-closed intermediate field of finite
transcendence degree containing the observable.  The differential field it generates is exactly
that, as soon as the observable is differentially algebraic: the generated field is derivation
closed by construction, its transcendence degree is finite precisely because a jet relation exists,
and the generator lies in it.

With the boundary theorem in the other direction this makes the interface an exact restatement of
differential algebraicity, rather than an extra hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Every differentially algebraic observable is a finite algebraic state observable.** -/
theorem finiteAlgebraicStateObservable_of_differentialAlgebraic
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] [CharZero E]
    {x : E} (hx : DifferentialAlgebraicOver F x) :
    FiniteAlgebraicStateObservable F x :=
  ⟨differentialAdjoin F ({x} : Set E),
    derivationClosed_differentialAdjoin F _,
    differentialAdjoin_trdeg_lt_aleph0_of_differentialAlgebraic hx,
    self_mem_differentialAdjoin x⟩

end GaloisForLFunctions.HTGeometry
