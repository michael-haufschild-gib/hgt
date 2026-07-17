import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import GaloisForLFunctions.HTGeometry.MatroidNatRank

/-!
# The transcendence-degree rank is a `Rank`

`mathlib`'s algebraic matroid `matroid R A` has independent sets the algebraically independent
subsets of `A`, and its cardinal rank is the transcendence degree.  Its finite rank function `eRk`
is monotone, submodular and bounded by cardinality — exactly the axioms of the abstract
`GaloisForLFunctions.MatroidGluing.Rank`.  This file packages it, giving a concrete instance of the
rank abstraction that drives the differential-matroid gluing engine: transcendence degree over a
fixed base field really is such a rank, so the abstraction is not vacuous.
-/

namespace GaloisForLFunctions.MatroidGluing

variable (R A : Type*) [CommRing R] [Field A] [Algebra R A] [FaithfulSMul R A] [DecidableEq A]

/-- Transcendence degree over `R`, as a rank on finite subsets of the field `A`:
`ρ(s)` is the matroid rank (= transcendence degree) of `s`.  Monotone, submodular, subcardinal. -/
noncomputable def transcendenceRank : Rank A :=
  matroidRank (AlgebraicIndependent.matroid R A)

end GaloisForLFunctions.MatroidGluing
