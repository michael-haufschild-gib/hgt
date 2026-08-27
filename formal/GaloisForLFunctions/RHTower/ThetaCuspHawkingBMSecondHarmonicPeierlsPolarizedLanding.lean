import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicOuterPolarizedReciprocity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonPolarizedSelector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingCubicPeierlsPolarization

/-!
# Corrected Peierls-polarized BM landing

Peierls skewness kills the mixed quadratic source's causal self-pairing.  The complete cubic cut
must instead be carried by the independent `++`--`--` quadratic-source polarization.  Exact BM
Schwarz radial reciprocity supplies its nonzero radial carrier: the regular/complementary
polarized current is the negative complementary horizon exponent.

Multiplying that current by the squared orthogonal-helicity coefficient and squared nonlinear
Einstein carrier gives a source-faithful candidate with critical-line zero locus.  When the actual
augmented Einstein--Teukolsky source pairing equals this explicit angular-radial factor, the full
cokernel causal cut equals the candidate and equality of total retarded and advanced sections is
equivalent to the critical line.

The source-pairing incidence remains a displayed premise.  Radial current conservation does not
by itself identify frequency-domain BM blocks with one global time-oriented Peierls propagator.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Exact regular `++`/Schwarz-complementary `--` BM polarized radial current. -/
def d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMSecondHarmonicPolarizedCurrent n chi
    (d4BMPlusPlusAdSOuterLinearCombination n chi
      (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi)
      (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi))
    (d4BMPlusPlusAdSOuterLinearCombinationDerivative n chi
      (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi)
      (d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi))
    (d4BMMinusMinusAdSOuterSchwarzLinearCombination n chi
      ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi))
      ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi)))
    (d4BMMinusMinusAdSOuterSchwarzLinearCombinationDerivative n chi
      ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi))
      ((starRingEnd ℂ) (d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi))) z

/-- Regular/Schwarz-complementary current is the exact negative complementary exponent. -/
theorem d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n chi z =
      -d4BMPlusPlusComplementaryFrobeniusExponent n chi := by
  exact d4BMSecondHarmonicRegularComplementaryPolarizedCurrent_eq_negExponent
    n chi hchi hz0 hz1

/-- Candidate full Peierls polarization: angular helicity norm, nonlinear carrier norm, and exact
BM Schwarz radial current, with the polarization factor two. -/
def d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) (z : ℝ) : ℂ :=
  2 * (Complex.normSq
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) *
    (Complex.normSq
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
        (xiSpectralPoint q)) : ℂ) *
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
      (d4BMXiMixedHorizonAngularMomentum q) z

/-- For a nonzero Einstein seed, exact BM Peierls candidate vanishes precisely on the critical
line. -/
theorem d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n amplitude q z = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hcarrier :=
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q
  have hcarrierNorm :
      (Complex.normSq
        (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
          (xiSpectralPoint q)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Complex.normSq_eq_zero.not).2 hcarrier
  have hcurrent :
      d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
          (d4BMXiMixedHorizonAngularMomentum q) z ≠ 0 := by
    rw [d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1]
    exact neg_ne_zero.mpr
      (d4BMXiPlusPlusRegularComplementaryWronskian_limit_ne_zero n q)
  rw [d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate,
    mul_eq_zero, mul_eq_zero, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, hcarrierNorm, hcurrent, or_false]
  rw [Complex.ofReal_eq_zero, Complex.normSq_eq_zero,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff]

/-- Under one explicit augmented source-pairing incidence, abstract Peierls polarization becomes
the exact BM angular-radial candidate. -/
theorem d4BMXiSecondHarmonicCokernelCausalCut_eq_PeierlsPolarizedCandidate
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) (z : ℝ)
    (hpm : RpmRet - RpmAdv = Delta)
    (hpp : RppRet - RppAdv = Delta)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y w, pairing x (B y w) = pairing w (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f)
    (hincidence :
      d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B m) =
        (Complex.normSq
          (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) *
        (Complex.normSq
          (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
            (xiSpectralPoint q)) : ℂ) *
        d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
          (d4BMXiMixedHorizonAngularMomentum q) z) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m =
      d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n amplitude q z := by
  rw [d4GaugeFixedTeukolskyCokernelCausalCut_eq_phaseNormalizedPeierls
      pairing B C Delta RppRet RpmRet RppAdv RpmAdv p m hpm hpp,
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized
      pairing B Delta p m hB hcyclic hskew,
    hincidence, d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate]
  ring

/-- Corrected conditional landing: equality of complete retarded and advanced nonlinear sections
is equivalent to criticality once the actual polarized Peierls source incidence is supplied. -/
theorem d4BMXiSecondHarmonic_retardedSection_eq_advancedSection_iff_criticalLine
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hpm : RpmRet - RpmAdv = Delta)
    (hpp : RppRet - RppAdv = Delta)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y w, pairing x (B y w) = pairing w (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f)
    (hincidence :
      d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B m) =
        (Complex.normSq
          (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) *
        (Complex.normSq
          (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
            (xiSpectralPoint q)) : ℂ) *
        d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
          (d4BMXiMixedHorizonAngularMomentum q) z) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
          (pairing m) B C RppRet RpmRet p m =
        d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
          (pairing m) B C RppAdv RpmAdv p m ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hcut := d4BMXiSecondHarmonicCokernelCausalCut_eq_PeierlsPolarizedCandidate
    pairing B C Delta RppRet RpmRet RppAdv RpmAdv p m
      n amplitude q z hpm hpp hB hcyclic hskew hincidence
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_section_sub]
    at hcut
  constructor
  · intro hsections
    apply (d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_eq_zero_iff
      ha n q hz0 hz1).mp
    rw [← hcut, hsections, sub_self]
  · intro hline
    have hzero :=
      (d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_eq_zero_iff
        ha n q hz0 hz1).mpr hline
    rw [← hcut, sub_eq_zero] at hzero
    exact hzero

end

end RHTower
