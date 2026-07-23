import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaInversion

/-!
# Multiple elliptic Gamma reflection--hypertranscendence universality

The all-order rank-three-minor theorem and the parity-correct inversion theorem concern the same
multiple elliptic Gamma product but were previously terminal in separate modules.  Their closure
classifies the reflection symmetry carried by a hypertranscendental meromorphic object at every
finite rank.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

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

/-- **Multiple elliptic Gamma reflection--hypertranscendence universality law.**  A finite
upper-half-plane period family containing one rank-three minor produces hypertranscendental
multiple elliptic Gamma and logarithmic-derivative meromorphic elements.  Simultaneously, the
pointwise product has the universal parity reflection law: even rank is a reciprocal cocycle and
has product one on the regular locus, while odd rank is reflection-fixed.  The logarithmic
derivative transforms uniformly by `(-1)^rank`. -/
theorem multipleEllipticGamma_rankThreeMinor_reflectionHypertranscendenceUniversality
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor τ) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero τ hτ) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero τ hτ) ∧
      (∀ z : ℂ,
        multipleEllipticGammaProduct τ ((∑ i, τ i) - z) =
          if Even (Fintype.card ι) then
            (multipleEllipticGammaProduct τ z)⁻¹
          else multipleEllipticGammaProduct τ z) ∧
      (∀ z : ℂ,
        multipleEllipticGammaForwardProduct τ z ≠ 0 →
        multipleEllipticGammaBackwardProduct τ z ≠ 0 →
        logDeriv (multipleEllipticGammaProduct τ) ((∑ i, τ i) - z) =
          multipleEllipticGammaLogSign ι *
            logDeriv (multipleEllipticGammaProduct τ) z) ∧
      (if Even (Fintype.card ι) then
        ∀ z : ℂ,
          multipleEllipticGammaForwardProduct τ z ≠ 0 →
          multipleEllipticGammaBackwardProduct τ z ≠ 0 →
          multipleEllipticGammaProduct τ z *
            multipleEllipticGammaProduct τ ((∑ i, τ i) - z) = 1
      else
        ∀ z : ℂ,
          multipleEllipticGammaProduct τ ((∑ i, τ i) - z) =
            multipleEllipticGammaProduct τ z) := by
  refine ⟨
    hypertranscendentalOver_multipleEllipticGammaMero_of_rankThreeMinor τ hτ hminor,
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor τ hτ hminor,
    multipleEllipticGammaProduct_reflection τ,
    ?_, ?_⟩
  · intro z hzF hzB
    exact logDeriv_multipleEllipticGammaProduct_reflection hτ hzF hzB
  · by_cases hcard : Even (Fintype.card ι)
    · simp only [hcard, if_true]
      intro z hzF hzB
      exact multipleEllipticGammaProduct_mul_reflection_of_even hcard hzF hzB
    · simp only [hcard, if_false]
      intro z
      simpa [hcard] using multipleEllipticGammaProduct_reflection τ z

end

end GaloisForLFunctions
