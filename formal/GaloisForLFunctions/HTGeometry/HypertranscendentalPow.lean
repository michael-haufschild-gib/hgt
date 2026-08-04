import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction

/-!
# Differential independence of a power

A differentially independent element is transcendental, so an algebraic element is differentially
algebraic.  Combined with the hypertranscendence of powers this gives the differential-independence
form used to build endomorphisms of a freely generated differential field: a positive power of a
differentially independent generator is again differentially independent.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

/-- **A differentially independent element is transcendental.**  Its jet family contains the element
itself, and an algebraically independent family has transcendental members. -/
theorem transcendental_of_differentialIndependent
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Differential R] {x : R}
    (hind : DifferentialIndependent A (fun _ : Unit ↦ x)) :
    Transcendental A x :=
  hind.algebraicIndependent.transcendental ()

/-- **An algebraic element is differentially algebraic.** -/
theorem differentialAlgebraicOver_of_isAlgebraic
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Differential R] {x : R}
    (hx : IsAlgebraic A x) :
    DifferentialAlgebraicOver A x :=
  fun hind ↦ transcendental_of_differentialIndependent hind hx

variable {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E]

/-- A positive power of a differentially independent generator is differentially independent. -/
theorem differentialIndependent_pow {g : E}
    (hg : DifferentialIndependent C (fun _ : Unit ↦ g)) {N : ℕ} (hN : 0 < N) :
    DifferentialIndependent C (fun _ : Unit ↦ g ^ N) := by
  rw [← hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact hypertranscendentalOver_pow_of_pos
    ((hypertranscendentalOver_iff_differentialIndependent_singleton C g).mpr hg) hN

end

end GaloisForLFunctions.HTGeometry
