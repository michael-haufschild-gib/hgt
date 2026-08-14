import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaGenericStructuralUniversalityLaw
import GaloisForLFunctions.HTGeometry.BottomFacePacketUnconditional

/-!
# Two distinct primes already make the multiple elliptic Gamma carrier hypertranscendental

The imaginary logarithms of distinct primes are integrally independent together with `1`, because a
rational relation between them would exponentiate to a multiplicative relation between distinct
primes.  Two of them therefore already contain a rank-three minor, and the period-rank dichotomy
turns that into hypertranscendence of both the raw carrier and its logarithmic derivative.

This is the finite-prime face of the occupation packets: no genericity hypothesis is left, only the
injectivity of the prime labelling and a packet of size at least two.

* `HTGeometry.multipleEllipticGammaHasRankThreeMinor_logPrimePeriod`;
* `HTGeometry.hypertranscendentalOver_multipleEllipticGammaMero_logPrime`.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

namespace HTGeometry

local instance multipleEllipticGammaReflectionHTUnivDomain :
    IsDomain (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTUnivDomain

local instance multipleEllipticGammaReflectionHTComplexAlgebraAnalytic :
    Algebra ℂ (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraAnalytic

local instance multipleEllipticGammaReflectionHTComplexAlgebraMero :
    Algebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraMero

local instance multipleEllipticGammaReflectionHTMeroDifferential :
    Differential (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroDifferential

local instance multipleEllipticGammaReflectionHTComplexDifferential : Differential ℂ :=
  multipleEllipticGammaHTComplexDifferential

local instance multipleEllipticGammaReflectionHTMeroCharZero :
    CharZero (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroCharZero

local instance multipleEllipticGammaReflectionHTComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexDifferentialAlgebra

local instance multipleEllipticGammaReflectionHTCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  multipleEllipticGammaHTCoordinateDifferential

local instance multipleEllipticGammaReflectionHTCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTCoordinateDifferentialAlgebra


variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Distinct prime logarithms contain a rank-three minor.** -/
theorem multipleEllipticGammaHasRankThreeMinor_logPrimePeriod (q : ι → Nat.Primes)
    (hq : Function.Injective q) (hcard : 2 ≤ Fintype.card ι) :
    MultipleEllipticGammaHasRankThreeMinor (logPrimePeriod q) :=
  multipleEllipticGammaHasRankThreeMinor_of_periodsIntegrallyIndependent (logPrimePeriod q)
    (periodsIntegrallyIndependent_logPrimePeriod hq) hcard

/-- **Finite-prime hypertranscendence.**  For an injective prime labelling of at least two
parameters, both the multiple elliptic Gamma carrier and its logarithmic derivative are
hypertranscendental over the meromorphic rational coordinate field. -/
theorem hypertranscendentalOver_multipleEllipticGammaMero_logPrime (q : ι → Nat.Primes)
    (hq : Function.Injective q) (hcard : 2 ≤ Fintype.card ι) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero (logPrimePeriod q) (logPrimePeriod_im_pos q)) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero (logPrimePeriod q) (logPrimePeriod_im_pos q)) := by
  have h := multipleEllipticGamma_rankThreeMinor_reflectionHypertranscendenceUniversality
    (logPrimePeriod q) (logPrimePeriod_im_pos q)
    (multipleEllipticGammaHasRankThreeMinor_logPrimePeriod q hq hcard)
  exact ⟨h.1, h.2.1⟩

/-- The two-prime case, with no index bookkeeping. -/
theorem hypertranscendentalOver_multipleEllipticGammaMero_twoLogPrime {p r : Nat.Primes}
    (hpr : p ≠ r) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero (twoLogPrimePeriods p r) (twoLogPrimePeriods_im_pos p r)) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero (twoLogPrimePeriods p r)
          (twoLogPrimePeriods_im_pos p r)) := by
  have hinj : Function.Injective fun x : Bool => if x then p else r := by
    intro x y hxy
    cases x <;> cases y <;> simp_all
  have hcard : 2 ≤ Fintype.card Bool := by simp
  exact hypertranscendentalOver_multipleEllipticGammaMero_logPrime
    (fun x : Bool => if x then p else r) hinj hcard

end HTGeometry

end

end GaloisForLFunctions
