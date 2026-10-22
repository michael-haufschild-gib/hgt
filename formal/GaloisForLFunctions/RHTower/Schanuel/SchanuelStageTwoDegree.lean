import GaloisForLFunctions.RHTower.Schanuel.SchanuelStageWitnesses
import GaloisForLFunctions.HTGeometry.TranscendenceDegreeOneVariable

/-!
# A stage-two counterexample has transcendence degree one

Hermite--Lindemann makes one of the two members of an exponential pair transcendental whenever the
exponent is nonzero, and rational linear independence forces both exponents to be nonzero.  So the
value field of a stage-two configuration always contains a transcendental element, and its
transcendence degree over the algebraic numbers is at least one.

Being below two, it is therefore exactly one: a stage-two counterexample is a one-variable object.
-/

namespace GaloisForLFunctions.RHTower

universe u

/-- Rational linear independence forces every member of the family to be nonzero. -/
theorem ne_zero_of_linearIndependent {ι : Type*} {x : ι → ℂ} (h : LinearIndependent ℚ x) (i : ι) :
    x i ≠ 0 := h.ne_zero i

/-- **The exponential pair always contributes a transcendental.**  This is Hermite--Lindemann in the
stagewise form already carried by the corpus. -/
theorem transcendental_or_transcendental_exp {z : ℂ} (hz : z ≠ 0) :
    Transcendental ℚ z ∨ Transcendental ℚ (Complex.exp z) :=
  schanuelExtractionAt_one_iff.mp schanuelExtractionAt_one z hz

/-- Transcendence over the rationals is transcendence over any algebraic base. -/
theorem transcendental_base_of_transcendental_rat {A K : Type u} [Field A] [Field K]
    [Algebra ℚ A] [Algebra ℚ K] [Algebra A K] [IsScalarTower ℚ A K]
    [Algebra.IsAlgebraic ℚ A] {z : K} (hz : Transcendental ℚ z) :
    Transcendental A z :=
  (Algebra.IsAlgebraic.transcendental_iff (R := ℚ) (S := A) (A := K)).mp hz

/-- **Clause 1 of the stage-two normal form.**  A value field with a transcendental element and
transcendence degree below two has transcendence degree exactly one. -/
theorem trdeg_eq_one_of_transcendental_of_lt_two {A K : Type u} [Field A] [Field K]
    [Algebra ℚ A] [Algebra ℚ K] [Algebra A K] [IsScalarTower ℚ A K]
    [Algebra.IsAlgebraic ℚ A] {z : K} (hz : Transcendental ℚ z)
    (hlt : Algebra.trdeg A K < 2) :
    Algebra.trdeg A K = 1 :=
  GaloisForLFunctions.HTGeometry.trdeg_eq_one_of_lt_two_of_transcendental
    (transcendental_base_of_transcendental_rat hz) hlt

end GaloisForLFunctions.RHTower
