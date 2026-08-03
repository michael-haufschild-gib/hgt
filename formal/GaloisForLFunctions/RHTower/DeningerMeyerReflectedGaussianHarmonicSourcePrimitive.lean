import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCompletedSourceGreen
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianPrimeGammaCauchyLanding
import GaloisForLFunctions.RHTower.DeningerPacketHodge
import GaloisForLFunctions.RHTower.DeningerMultiplier

/-!
# Harmonic-source realization of the reflected-Gaussian Green primitive

The completed Green primitive was constructed abstractly on the source Hilbert middle as the
coefficient field `-epsilon(q) h_ref(q)`.  This file identifies that field with the already
physical Deninger harmonic Hodge operator `W = i sign(D)`.

The point is arithmetic rather than a change of notation.  On an actual Xi divisor copy, the
lexicographic functional-equation orientation never reaches its fallback branch: the real part of
the centered spectral coordinate is the nonzero ordinate of the original Xi zero.  Therefore the
orientation is exactly the sign of the genuine source frequency.  The completed Green primitive
is consequently `i W h_ref`, so it is obtained by an unconditional source-side Fourier multiplier
before any divisor incidence or Hellinger--Gamma quotient.
-/

open Complex

namespace RHTower

noncomputable section

/-- On the actual Xi divisor, functional-equation orientation is the sign of the original
nonzero harmonic frequency.  In particular, the lexicographic fallback in the abstract orbit
orientation is never used. -/
theorem deningerArithmeticFEOrientation_eq_deningerFreqSign
    (q : XiZeroCopy) :
    deningerArithmeticFEOrientation q =
      ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) := by
  have him : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint]
  rw [deningerArithmeticFEOrientation, hre, deningerFreqSign]
  by_cases hpos : 0 < (q.1 : ℂ).im
  · simp [hpos]
  · have hneg : (q.1 : ℂ).im < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) him
    simp [hpos, hneg]

/-- The physical harmonic Hodge multiplier on the multiplicity-exact Xi source carrier. -/
def deningerXiHarmonicHodgeWeight (q : XiZeroCopy) : ℂ :=
  Complex.I * ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ)

@[simp]
theorem norm_deningerXiHarmonicHodgeWeight (q : XiZeroCopy) :
    ‖deningerXiHarmonicHodgeWeight q‖ = 1 := by
  rw [deningerXiHarmonicHodgeWeight, norm_mul, norm_I]
  simp only [one_mul, norm_real, Real.norm_eq_abs, deningerFreqSign]
  split_ifs <;> norm_num

/-- The Deninger operator `W = i sign(D)` as a continuous source-Hilbert multiplier. -/
def deningerXiHarmonicHodge : XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  deningerMultiplier (fun q => (norm_deningerXiHarmonicHodgeWeight q).le)

@[simp]
theorem deningerXiHarmonicHodge_apply (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerXiHarmonicHodge a q =
      Complex.I * ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) * a q := by
  rfl

/-- The Hilbert multiplier is exactly the pointwise packet Hodge operator already constructed
from leafwise harmonic modes. -/
theorem deningerXiHarmonicHodge_eq_deningerHodgeW
    (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerXiHarmonicHodge a q =
      deningerHodgeW (fun r : XiZeroCopy => (r.1 : ℂ).im) a q := by
  rfl

/-- The physical harmonic Hodge operator has the weight-one square law on the completed source. -/
theorem deningerXiHarmonicHodge_sq (a : XiDivisorL2) :
    deningerXiHarmonicHodge (deningerXiHarmonicHodge a) = -a := by
  ext q
  rw [deningerXiHarmonicHodge_apply, deningerXiHarmonicHodge_apply]
  have hsign :
      (((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ)) = 1 := by
    exact_mod_cast deningerFreqSign_sq (q.1 : ℂ).im
  have hI : Complex.I * Complex.I = -1 := by
    simpa only [pow_two] using Complex.I_sq
  change Complex.I * _ * (Complex.I * _ * a q) = -a q
  calc
    Complex.I * _ * (Complex.I * _ * a q) =
        (Complex.I * Complex.I) *
          (((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
            ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ)) * a q := by ring
    _ = -a q := by rw [hI, hsign]; ring

namespace DeningerMeyerGaussianGreen

/-- The unique completed Green primitive is not an arbitrary divisor-side coefficient choice:
it is `i` times the physical harmonic Hodge transform of the fixed reflected Meyer Gaussian. -/
theorem reflectedGaussianHorizonCompletedGreenPrimitive_eq_harmonicHodge :
    reflectedGaussianHorizonCompletedGreenPrimitive =
      Complex.I • deningerXiHarmonicHodge reflectedGaussianHorizonAdmittedResidue := by
  ext q
  rw [reflectedGaussianHorizonCompletedGreenPrimitive_apply,
    lp.coeFn_smul, Pi.smul_apply, deningerXiHarmonicHodge_apply,
    reflectedGaussianHorizonAdmittedResidue_apply,
    deningerArithmeticFEOrientation_eq_deningerFreqSign]
  have hI : Complex.I * Complex.I = -1 := by
    simpa only [pow_two] using Complex.I_sq
  rw [smul_eq_mul]
  calc
    -((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        reflectedGaussianHorizonGrade q =
      (Complex.I * Complex.I) *
        (((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
          reflectedGaussianHorizonGrade q) := by rw [hI]; ring
    _ = Complex.I *
        (Complex.I * ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
          reflectedGaussianHorizonGrade q) := by ring

/-- Equivalent pointwise form: the completed primitive is the physical source-frequency sign
times the reflected Gaussian coefficient. -/
theorem reflectedGaussianHorizonCompletedGreenPrimitive_apply_frequencySign
    (q : XiZeroCopy) :
    reflectedGaussianHorizonCompletedGreenPrimitive q =
      -((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        reflectedGaussianHorizonGrade q := by
  rw [reflectedGaussianHorizonCompletedGreenPrimitive_apply,
    deningerArithmeticFEOrientation_eq_deningerFreqSign]

/-- Concrete oriented prime--Gamma boundary source.  Harmonic orientation is applied before
Bochner integration and before restriction to any Hellinger--Gamma or Calderon--Witt quotient. -/
def reflectedGaussianPrimeGammaOrientedCauchyBoundary (x : ℝ) : XiDivisorL2 :=
  (Complex.I • deningerXiHarmonicHodge)
    (reflectedGaussianPrimeGammaCauchyBoundary x)

theorem integrable_reflectedGaussianPrimeGammaOrientedCauchyBoundary :
    MeasureTheory.Integrable reflectedGaussianPrimeGammaOrientedCauchyBoundary := by
  exact (Complex.I • deningerXiHarmonicHodge).integrable_comp
    integrable_reflectedGaussianPrimeGammaCauchyBoundary

/-- The explicit oriented two-line prime--Gamma source integrates to the unique completed Green
primitive.  This is the promised pre-divisor source realization, not a coefficient interpolation
performed after the Xi divisor has been enumerated. -/
theorem integral_reflectedGaussianPrimeGammaOrientedCauchyBoundary_eq_greenPrimitive :
    (∫ x : ℝ, reflectedGaussianPrimeGammaOrientedCauchyBoundary x) =
      reflectedGaussianHorizonCompletedGreenPrimitive := by
  let W : XiDivisorL2 →L[ℂ] XiDivisorL2 :=
    Complex.I • deningerXiHarmonicHodge
  have hcomm := W.integral_comp_comm
    integrable_reflectedGaussianPrimeGammaCauchyBoundary
  have hgrade : reflectedGaussianHorizonGradeL2 =
      reflectedGaussianHorizonAdmittedResidue := by
    ext q
    rw [reflectedGaussianHorizonGradeL2_apply,
      reflectedGaussianHorizonAdmittedResidue_apply]
  change (∫ x : ℝ, W (reflectedGaussianPrimeGammaCauchyBoundary x)) = _
  rw [hcomm, integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2,
    hgrade]
  exact reflectedGaussianHorizonCompletedGreenPrimitive_eq_harmonicHodge.symm

end DeningerMeyerGaussianGreen

end

end RHTower
