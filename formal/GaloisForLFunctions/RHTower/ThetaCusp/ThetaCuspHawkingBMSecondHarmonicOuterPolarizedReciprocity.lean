import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicOuterResponseKrein
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicProjectiveCausalNoGo

/-!
# Exact BM radial-to-boundary polarized reciprocity

Arbitrary source/response vectors in exact AdS outer basis define genuine `++` and Schwarz `--`
solution jets. Their polarized radial current equals exact AdS boundary concomitant at every
interior radius because outer normalized Wronskian is globally `-1/2`. Consequently radial current
has exact phase-normalized advanced-minus-retarded response factorization without taking a
singular endpoint limit.

Derivation of augmented Einstein retarded and advanced response values remains separate.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Arbitrary source/response combination in exact `++` AdS outer basis. -/
def d4BMPlusPlusAdSOuterLinearCombination
    (n : ℕ) (chi source response : ℂ) : ℝ → ℂ := fun z =>
  source * d4BMPlusPlusAdSForbiddenSolution n chi z +
    response * d4BMPlusPlusAdSNormalizableSolution n chi z

/-- Declared first jet of arbitrary `++` AdS outer combination. -/
def d4BMPlusPlusAdSOuterLinearCombinationDerivative
    (n : ℕ) (chi source response : ℂ) : ℝ → ℂ := fun z =>
  source * d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z +
    response * d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z

/-- Declared second jet of arbitrary `++` AdS outer combination. -/
def d4BMPlusPlusAdSOuterLinearCombinationSecondDerivative
    (n : ℕ) (chi source response : ℂ) : ℝ → ℂ := fun z =>
  source * d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z +
    response * d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z

/-- Arbitrary `--` outer combination in Schwarz-conjugate exact AdS basis. -/
def d4BMMinusMinusAdSOuterSchwarzLinearCombination
    (n : ℕ) (chi source response : ℂ) : ℝ → ℂ := fun z =>
  source * (starRingEnd ℂ) (d4BMPlusPlusAdSForbiddenSolution n chi z) +
    response * (starRingEnd ℂ) (d4BMPlusPlusAdSNormalizableSolution n chi z)

/-- Declared first jet of arbitrary Schwarz `--` outer combination. -/
def d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative
    (n : ℕ) (chi source response : ℂ) : ℝ → ℂ := fun z =>
  source * (starRingEnd ℂ) (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z) +
    response * (starRingEnd ℂ) (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z)

/-- Declared second jet of arbitrary Schwarz `--` outer combination. -/
def d4BMMinusMinusAdSOuterSchwarzLinearCombinationSecondDerivative
    (n : ℕ) (chi source response : ℂ) : ℝ → ℂ := fun z =>
  source * (starRingEnd ℂ) (d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z) +
    response * (starRingEnd ℂ) (d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z)

/-- First declared `++` outer-combination jet is its actual radial derivative. -/
theorem hasDerivAt_d4BMPlusPlusAdSOuterLinearCombination
    (n : ℕ) (chi source response : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusAdSOuterLinearCombination n chi source response)
      (d4BMPlusPlusAdSOuterLinearCombinationDerivative n chi source response z) z := by
  simpa [d4BMPlusPlusAdSOuterLinearCombination, d4BMPlusPlusAdSOuterLinearCombinationDerivative] using!
    ((hasDerivAt_d4BMPlusPlusAdSForbiddenSolution n chi hchi hz0 hz1).const_mul source).add
      ((hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi hz0 hz1).const_mul response)

/-- Second declared `++` outer-combination jet is actual derivative of first. -/
theorem hasDerivAt_d4BMPlusPlusAdSOuterLinearCombinationDerivative
    (n : ℕ) (chi source response : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusAdSOuterLinearCombinationDerivative n chi source response)
      (d4BMPlusPlusAdSOuterLinearCombinationSecondDerivative n chi source response z) z := by
  simpa [d4BMPlusPlusAdSOuterLinearCombinationDerivative,
    d4BMPlusPlusAdSOuterLinearCombinationSecondDerivative] using!
    ((hasDerivAt_d4BMPlusPlusAdSForbiddenSolutionDerivative
      n chi hchi hz0 hz1).const_mul source).add
      ((hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative
        n chi hchi hz0 hz1).const_mul response)

/-- First declared Schwarz `--` outer-combination jet is its actual radial derivative. -/
theorem hasDerivAt_d4BMMinusMinusAdSOuterSchwarzLinearCombination
    (n : ℕ) (chi source response : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMMinusMinusAdSOuterSchwarzLinearCombination n chi source response)
      (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n chi source response z) z := by
  have hS := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_d4BMPlusPlusAdSForbiddenSolution n chi hchi hz0 hz1)
  have hV := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi hz0 hz1)
  simpa [d4BMMinusMinusAdSOuterSchwarzLinearCombination,
    d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative] using!
      (hS.const_mul source).add (hV.const_mul response)

/-- Second declared Schwarz `--` outer-combination jet is actual derivative of first. -/
theorem hasDerivAt_d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative
    (n : ℕ) (chi source response : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n chi source response)
      (d4BMMinusMinusAdSOuterSchwarzLinearCombinationSecondDerivative n chi source response z) z := by
  have hS := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_d4BMPlusPlusAdSForbiddenSolutionDerivative n chi hchi hz0 hz1)
  have hV := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative n chi hchi hz0 hz1)
  simpa [d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative,
    d4BMMinusMinusAdSOuterSchwarzLinearCombinationSecondDerivative] using!
      (hS.const_mul source).add (hV.const_mul response)

/-- Every exact `++` outer linear combination solves BM radial equation. -/
theorem d4BMPlusPlusAdSOuterLinearCombination_jet_eq_zero
    (n : ℕ) (chi source response : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusAdSOuterLinearCombination n chi source response z)
      (d4BMPlusPlusAdSOuterLinearCombinationDerivative n chi source response z)
      (d4BMPlusPlusAdSOuterLinearCombinationSecondDerivative n chi source response z) = 0 := by
  have hS := d4BMPlusPlusAdSForbiddenSolution_jet_eq_zero n chi hchi hz0 hz1
  have hV := d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n chi hchi hz0 hz1
  rw [d4BMPlusPlusAdSOuterLinearCombination, d4BMPlusPlusAdSOuterLinearCombinationDerivative,
    d4BMPlusPlusAdSOuterLinearCombinationSecondDerivative, d4BMPlusPlusHypergeometricJet]
  rw [d4BMPlusPlusHypergeometricJet] at hS hV
  linear_combination source * hS + response * hV

/-- Every exact Schwarz outer combination solves conjugate `--` BM radial equation. -/
theorem d4BMMinusMinusAdSOuterSchwarzLinearCombination_jet_eq_zero
    (n : ℕ) (chi source response : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMMinusMinusHypergeometricJet n ((starRingEnd ℂ) chi) z
      (d4BMMinusMinusAdSOuterSchwarzLinearCombination n chi source response z)
      (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n chi source response z)
      (d4BMMinusMinusAdSOuterSchwarzLinearCombinationSecondDerivative n chi source response z) = 0 := by
  apply (starRingEnd ℂ).injective
  rw [map_zero, d4BMMinusMinusHypergeometricJet_schwarz]
  simp only [d4BMMinusMinusAdSOuterSchwarzLinearCombination,
    d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative,
    d4BMMinusMinusAdSOuterSchwarzLinearCombinationSecondDerivative,
    map_add, map_mul, Complex.conj_conj]
  exact d4BMPlusPlusAdSOuterLinearCombination_jet_eq_zero n chi
    ((starRingEnd ℂ) source) ((starRingEnd ℂ) response) hchi hz0 hz1

/-- Exact polarized radial current equals AdS boundary concomitant at every interior radius. -/
theorem d4BMSecondHarmonicOuterPolarizedCurrent_eq_boundaryConcomitant
    (n : ℕ) (chi sourcePP responsePP sourceMM responseMM : ℂ)
    (hchi : chi.re ≠ 0) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMSecondHarmonicPolarizedCurrent n chi
        (d4BMPlusPlusAdSOuterLinearCombination n chi sourcePP responsePP)
        (d4BMPlusPlusAdSOuterLinearCombinationDerivative n chi sourcePP responsePP)
        (d4BMMinusMinusAdSOuterSchwarzLinearCombination n chi sourceMM responseMM)
        (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n chi sourceMM responseMM) z =
      d4BMAdSBoundaryPolarizedConcomitant
        sourcePP responsePP sourceMM responseMM := by
  have hW := d4BMPlusPlusAdSOuterWronskian_eq_neg_half
    n chi hchi hz0 hz1
  rw [d4BMPlusPlusAdSOuterWronskian, d4BMPlusPlusNormalizedWronskian] at hW
  unfold d4BMSecondHarmonicPolarizedCurrent
    d4BMPlusPlusAdSOuterLinearCombination d4BMPlusPlusAdSOuterLinearCombinationDerivative
    d4BMMinusMinusAdSOuterSchwarzLinearCombination d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative
    d4BMAdSBoundaryPolarizedConcomitant
  simp only [Pi.mul_apply, map_add, map_mul, Complex.conj_conj]
  linear_combination
    ((starRingEnd ℂ sourceMM) * responsePP -
      (starRingEnd ℂ responseMM) * sourcePP) * hW

/-- Exact radial current factors through phase-normalized advanced-minus-retarded response. -/
theorem d4BMSecondHarmonicOuterPolarizedCurrent_eq_responseJump
    (n : ℕ) (chi sourcePP responsePP sourceMM responseMM
      retardedResponse advancedResponse : ℂ)
    (hchi : chi.re ≠ 0) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hpp : responsePP = retardedResponse * sourcePP)
    (hmm : responseMM = (starRingEnd ℂ) advancedResponse * sourceMM) :
    d4BMSecondHarmonicPolarizedCurrent n chi
        (d4BMPlusPlusAdSOuterLinearCombination n chi sourcePP responsePP)
        (d4BMPlusPlusAdSOuterLinearCombinationDerivative n chi sourcePP responsePP)
        (d4BMMinusMinusAdSOuterSchwarzLinearCombination n chi sourceMM responseMM)
        (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n chi sourceMM responseMM) z =
      (starRingEnd ℂ) sourceMM * sourcePP *
        (advancedResponse - retardedResponse) / 2 := by
  rw [d4BMSecondHarmonicOuterPolarizedCurrent_eq_boundaryConcomitant n chi sourcePP responsePP
    sourceMM responseMM hchi hz0 hz1]
  exact d4BMAdSBoundaryPolarizedConcomitant_eq_responseJump
    sourcePP responsePP sourceMM responseMM retardedResponse advancedResponse hpp hmm

/-- Regular/Schwarz-complementary radial current is exact negative horizon exponent. -/
theorem d4BMSecondHarmonicRegularComplementaryPolarizedCurrent_eq_negExponent
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMSecondHarmonicPolarizedCurrent n chi
        (d4BMPlusPlusAdSOuterLinearCombination n chi
          (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi)
          (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi))
        (d4BMPlusPlusAdSOuterLinearCombinationDerivative n chi
          (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi)
          (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi))
        (d4BMMinusMinusAdSOuterSchwarzLinearCombination n chi
          ((starRingEnd ℂ)
            (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi))
          ((starRingEnd ℂ)
            (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi)))
        (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n chi
          ((starRingEnd ℂ)
            (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi))
          ((starRingEnd ℂ)
            (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi))) z =
      -d4BMPlusPlusComplementaryFrobeniusExponent n chi := by
  rw [d4BMSecondHarmonicOuterPolarizedCurrent_eq_boundaryConcomitant
    n chi
    (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi)
    (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi)
    ((starRingEnd ℂ)
      (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi))
    ((starRingEnd ℂ)
      (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi))
    hchi hz0 hz1,
    d4BMAdSBoundaryPolarizedConcomitant,
    Complex.conj_conj, Complex.conj_conj]
  have hdet := d4BMPlusPlusAdSConnectionDet_eq n chi hchi
  linear_combination (1 / 2 : ℂ) * hdet

/-- Every Xi fibre has nonzero regular/Schwarz-complementary polarized radial carrier. -/
theorem d4BMXiSecondHarmonicRegularComplementaryPolarizedCurrent_ne_zero
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMSecondHarmonicPolarizedCurrent n (d4BMXiMixedHorizonAngularMomentum q)
        (d4BMPlusPlusAdSOuterLinearCombination n (d4BMXiMixedHorizonAngularMomentum q)
          (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q)))
        (d4BMPlusPlusAdSOuterLinearCombinationDerivative n
          (d4BMXiMixedHorizonAngularMomentum q)
          (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q)))
        (d4BMMinusMinusAdSOuterSchwarzLinearCombination n
          (d4BMXiMixedHorizonAngularMomentum q)
          ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q)))
          ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q))))
        (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n
          (d4BMXiMixedHorizonAngularMomentum q)
          ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q)))
          ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q)))) z ≠ 0 := by
  rw [d4BMSecondHarmonicRegularComplementaryPolarizedCurrent_eq_negExponent n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1]
  exact neg_ne_zero.mpr (d4BMXiPlusPlusRegularComplementaryWronskian_limit_ne_zero n q)

end

end RHTower
