import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingNonlinearBoundaryHelicityFluxDichotomy

/-!
# BM mixed-horizon causal optical producer

Multiply the exact orthogonal-helicity coefficient by the horizon component of the actual
gauge-fixed BM second-harmonic radiation map. Its squared modulus is exactly the horizon
orthogonal-helicity flux. Multiplication by the positive BM mixed-horizon Frobenius monodromy gives
a causal optical section with nonnegative imaginary part, strictly positive at every off-critical
Xi divisor.

For the total nonlinear `++-` Schur source, this optical section is obtained from two precise
dynamical identities: the mixed retarded-minus-advanced response is the Frobenius monodromy mode,
and cyclic Einstein--Green reciprocity identifies its cokernel coupling with the optical squared
modulus. Under those identities, simultaneous retarded and advanced Fredholm solvability forces
the critical line. The common direct third Einstein jet is absent from the causal cut.

The positive-imaginary statement applies on the real-momentum Sturm slice. For an actual Xi fibre
the BM momentum is complex. Its analytically continued Frobenius monodromy is still nonzero, so
the causal section retains the same critical-line zero locus without asserting an off-slice sign.
-/

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Angular-compatible optical projection of the nonlinear normalizable BM radiation. -/
def d4BMMixedHorizonOpticalSourceProjection
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q *
    (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
      amplitude orthogonalMixing q) 0

/-- The horizon source projection contains the exact ingoing Green coefficient and self-dual
Einstein carrier; the arbitrary non-self-dual source coordinate is absent. -/
theorem d4BMMixedHorizonOpticalSourceProjection_eq
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q =
      d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q *
        (d4BMGaugeFixedSecondHarmonicGreen q *
          d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
            (xiSpectralPoint q)) := by
  simp [d4BMMixedHorizonOpticalSourceProjection,
    d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation,
    d4BMGaugeFixedSecondHarmonicRadiationMap]

/-- Exact three-factor horizon Gram: angular mixing, ingoing BM Green transfer, and nonlinear
Einstein carrier. -/
theorem normSq_d4BMMixedHorizonOpticalSourceProjection_factorization
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q) =
      Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) *
        Complex.normSq (d4BMGaugeFixedSecondHarmonicGreen q) *
          Complex.normSq
            (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
              (xiSpectralPoint q)) := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq,
    Complex.normSq_mul, Complex.normSq_mul]
  ring

/-- The source projection squared modulus is exactly the gauge-fixed horizon helicity flux. -/
theorem normSq_d4BMMixedHorizonOpticalSourceProjection
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q) =
      d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux
        amplitude orthogonalMixing q := by
  rw [d4BMMixedHorizonOpticalSourceProjection, Complex.normSq_mul,
    normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient]
  simp [d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux,
    d4ThetaTeukolskyOrthogonalHelicityMixingEnergy, Complex.sq_norm]

/-- Contact-free candidate causal section fixed by BM horizon monodromy and the optical Gram. -/
def d4BMMixedHorizonCausalOpticalSection
    (n k : ℕ) (chi : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi *
    Complex.normSq
      (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q)

/-- Exact optical form: the causal section is `i` times positive Frobenius weight times
orthogonal-helicity horizon flux. -/
theorem d4BMMixedHorizonCausalOpticalSection_eq_imaginaryFlux
    (n k : ℕ) (chi : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonCausalOpticalSection
        n k chi amplitude orthogonalMixing q =
      Complex.I * ((2 * Real.pi *
        d4BMMixedHorizonFrobeniusWeight n k chi *
        d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux
          amplitude orthogonalMixing q : ℝ) : ℂ) := by
  rw [d4BMMixedHorizonCausalOpticalSection,
    d4BMMixedHorizonCounterclockwiseMonodromyJump_eq,
    normSq_d4BMMixedHorizonOpticalSourceProjection]
  push_cast
  ring

/-- BM mixed-horizon causal optical section has nonnegative imaginary part. -/
theorem d4BMMixedHorizonCausalOpticalSection_im_nonneg
    (n k : ℕ) (chi : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    0 ≤ (d4BMMixedHorizonCausalOpticalSection
      n k chi amplitude orthogonalMixing q).im := by
  rw [d4BMMixedHorizonCausalOpticalSection_eq_imaginaryFlux]
  simp
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (le_of_lt (d4BMMixedHorizonFrobeniusWeight_pos n k chi)))
    (d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux_nonneg
      amplitude orthogonalMixing q)

/-- With a nonzero nonlinear seed, the causal optical section vanishes exactly on the critical
line. -/
theorem d4BMMixedHorizonCausalOpticalSection_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (chi : ℝ) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonCausalOpticalSection
        n k chi amplitude orthogonalMixing q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMMixedHorizonCausalOpticalSection,
    normSq_d4BMMixedHorizonOpticalSourceProjection, mul_eq_zero]
  simp only [d4BMMixedHorizonCounterclockwiseMonodromyJump_ne_zero,
    Complex.ofReal_eq_zero, false_or]
  exact d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux_eq_zero_iff
    ha orthogonalMixing q

/-- Every off-critical divisor gives a strictly positive causal spectral density. -/
theorem d4BMMixedHorizonCausalOpticalSection_im_pos_of_offCritical
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (chi : ℝ) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < (d4BMMixedHorizonCausalOpticalSection
      n k chi amplitude orthogonalMixing q).im := by
  rw [d4BMMixedHorizonCausalOpticalSection_eq_imaginaryFlux]
  simp
  apply mul_pos
  · exact mul_pos (by positivity)
      (d4BMMixedHorizonFrobeniusWeight_pos n k chi)
  · have hflux :=
      (d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux_eq_zero_iff
        ha orthogonalMixing q).not.mpr hoff
    exact lt_of_le_of_ne
      (d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux_nonneg
        amplitude orthogonalMixing q) (Ne.symm hflux)

/-- Actual Xi-fibre causal optical section with complex BM angular momentum. -/
def d4BMXiMixedHorizonCausalOpticalSection
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiMixedHorizonComplexMonodromyJump n k q *
    Complex.normSq
      (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q)

/-- Analytically continued radial monodromy is nonzero, so the actual Xi-fibre optical section
vanishes exactly with the horizon helicity flux. -/
theorem d4BMXiMixedHorizonCausalOpticalSection_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonCausalOpticalSection
        n k amplitude orthogonalMixing q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiMixedHorizonCausalOpticalSection,
    normSq_d4BMMixedHorizonOpticalSourceProjection, mul_eq_zero]
  simp only [d4BMXiMixedHorizonComplexMonodromyJump_ne_zero,
    Complex.ofReal_eq_zero, false_or]
  exact d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux_eq_zero_iff
    ha orthogonalMixing q

/-- Complex-momentum mixed response incidence plus horizon Einstein--Green reciprocity identify
the complete nonlinear causal cut with the actual Xi-fibre optical section. -/
theorem d4BMXiMixedHorizon_totalCokernelCausalCut_eq_opticalSection
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMXiMixedHorizonComplexMonodromyJump n k q • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0)
    (hreciprocity : ell (B p u) =
      Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q)) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m =
      d4BMXiMixedHorizonCausalOpticalSection
        n k amplitude orthogonalMixing q := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq,
    hpm, hpp]
  simp [map_smul, hreciprocity, d4BMXiMixedHorizonCausalOpticalSection]

/-- On an actual complex Xi fibre, simultaneous retarded and advanced nonlinear solvability still
forces the critical line; no off-slice positivity assumption is used. -/
theorem d4BMXiMixedHorizon_simultaneousCausalSolvability_forces_criticalLine
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMXiMixedHorizonComplexMonodromyJump n k q • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0)
    (hreciprocity : ell (B p u) =
      Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q))
    (hret : d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
      ell B C RppRet RpmRet p m = 0)
    (hadv : d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
      ell B C RppAdv RpmAdv p m = 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply (d4BMXiMixedHorizonCausalOpticalSection_eq_zero_iff
    ha n k orthogonalMixing q).mp
  rw [← d4BMXiMixedHorizon_totalCokernelCausalCut_eq_opticalSection
    ell B C RppRet RpmRet RppAdv RpmAdv p m u n k
      amplitude orthogonalMixing q hpm hpp hreciprocity,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_section_sub,
    hret, hadv, sub_self]

/-- Under the exact mixed response and horizon reciprocity identities, equality of the full
retarded and advanced nonlinear sections is equivalent to the critical line. Off line, the total
causal asymmetry is forced and cannot be repaired by the common direct third Einstein jet. -/
theorem d4BMXiMixedHorizon_retardedSection_eq_advancedSection_iff
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMXiMixedHorizonComplexMonodromyJump n k q • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0)
    (hreciprocity : ell (B p u) =
      Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q)) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
          ell B C RppRet RpmRet p m =
        d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
          ell B C RppAdv RpmAdv p m ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hcut := d4BMXiMixedHorizon_totalCokernelCausalCut_eq_opticalSection
    ell B C RppRet RpmRet RppAdv RpmAdv p m u n k
      amplitude orthogonalMixing q hpm hpp hreciprocity
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_section_sub]
    at hcut
  constructor
  · intro hsections
    apply (d4BMXiMixedHorizonCausalOpticalSection_eq_zero_iff
      ha n k orthogonalMixing q).mp
    rw [← hcut, hsections, sub_self]
  · intro hline
    have hzero := (d4BMXiMixedHorizonCausalOpticalSection_eq_zero_iff
      ha n k orthogonalMixing q).mpr hline
    rw [← hcut, sub_eq_zero] at hzero
    exact hzero

/-- Mixed Frobenius response incidence plus Einstein--Green reciprocity identify the complete
nonlinear cokernel causal cut with the optical section. -/
theorem d4BMMixedHorizon_totalCokernelCausalCut_eq_opticalSection
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    (n k : ℕ) (chi : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0)
    (hreciprocity : ell (B p u) =
      Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q)) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m =
      d4BMMixedHorizonCausalOpticalSection
        n k chi amplitude orthogonalMixing q := by
  rw [d4BMMixedHorizonMonodromy_totalCokernelCausalCut
    ell B C RppRet RpmRet RppAdv RpmAdv p m u n k chi hpm hpp,
    hreciprocity]
  rfl

/-- Simultaneous retarded and advanced nonlinear Fredholm solvability forces zero orthogonal
helicity flux, hence the critical line. -/
theorem d4BMMixedHorizon_simultaneousCausalSolvability_forces_criticalLine
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m u : X)
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n k : ℕ) (chi : ℝ) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) =
        d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi • u)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0)
    (hreciprocity : ell (B p u) =
      Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q))
    (hret : d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
      ell B C RppRet RpmRet p m = 0)
    (hadv : d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
      ell B C RppAdv RpmAdv p m = 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply (d4BMMixedHorizonCausalOpticalSection_eq_zero_iff
    ha n k chi orthogonalMixing q).mp
  rw [← d4BMMixedHorizon_totalCokernelCausalCut_eq_opticalSection
    ell B C RppRet RpmRet RppAdv RpmAdv p m u n k chi
      amplitude orthogonalMixing q hpm hpp hreciprocity,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_section_sub,
    hret, hadv, sub_self]

end
end RHTower
