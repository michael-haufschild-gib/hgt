import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenBootstrap

/-!
# The normalized prime--archimedean source value as a Witten-state functional

The exact Born/Witten amplitudes carry the complete theta source.  This file packages their
position moments and identifies the first nontrivial normalized prime--archimedean moment with
one explicit quadratic functional of those pure-state moments.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The complete `2j`-th position moment of the countable theta Born/Witten state family. -/
def thetaCuspBornWittenRawMoment (j : ℕ) : ℝ :=
  ∑' n : ℕ, 2 * Real.pi *
    ∫ x : ℝ in Ioi 0,
      x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)

/-- The Born/Witten raw moments are exactly the theta-cusp raw moments. -/
theorem thetaCuspBornWittenRawMoment_eq_thetaCuspRawEvenMoment (j : ℕ) :
    thetaCuspBornWittenRawMoment j = thetaCuspRawEvenMoment j := by
  rw [thetaCuspBornWittenRawMoment,
    thetaCuspRawEvenMoment_eq_tsum_integral_bornWittenAmplitude_sq]

/-- The source-side quadratic functional selected by the first nontrivial centered trace
moment. -/
def thetaCuspBornWittenQuadraticSource : ℝ :=
  (thetaCuspBornWittenRawMoment 1 / thetaCuspBornWittenRawMoment 0) ^ (2 : ℕ) / 2 -
    (thetaCuspBornWittenRawMoment 2 / thetaCuspBornWittenRawMoment 0) / 6

/-- The first nontrivial normalized prime--archimedean moment is exactly the quadratic
Born/Witten position-moment functional. -/
theorem normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource :
    normalizedPrimeArchMoment 1 = thetaCuspBornWittenQuadraticSource := by
  rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]
  simp only [thetaCuspNormalizedEvenMoment, thetaCuspBornWittenQuadraticSource]
  rw [thetaCuspBornWittenRawMoment_eq_thetaCuspRawEvenMoment,
    thetaCuspBornWittenRawMoment_eq_thetaCuspRawEvenMoment,
    thetaCuspBornWittenRawMoment_eq_thetaCuspRawEvenMoment]

end

end RHTower
