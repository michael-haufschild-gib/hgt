import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource
import GaloisForLFunctions.RHTower.PrimeArchReciprocalSquareSectorGate
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# Positive-paired diagonal and reciprocal-square sector

The diagonal of the one-sided Schwarz-paired continued Cauchy kernel is exactly the
reciprocal-square sector observable.  This is the algebraic bridge behind the paper-level
reduction from matrix passivity to a scalar continued prime--Gamma sign condition.

The theorem is source-pure: it uses only the two already defined continued-source value
functions.  It does not assert the sign of either side.
-/

open Complex

namespace RHTower

noncomputable section

/-- Away from the centered origin, the continued reciprocal-square trace is exactly the
normalized prime--archimedean moment germ. -/
theorem continuedPrimeArchReciprocalSquareTrace_eq_normalizedPrimeArchMomentGerm
    {z : ℂ} (hz : z ≠ 0) :
    continuedPrimeArchReciprocalSquareTrace z =
      normalizedPrimeArchMomentGerm z := by
  rw [continuedPrimeArchReciprocalSquareTrace, normalizedPrimeArchMomentGerm,
    normalizedTraceMomentGerm, dslope_of_ne _ hz, slope_def_module,
    continuedPrimeArchSourceRelativeTrace_zero]
  simp only [sub_zero, smul_eq_mul]
  field_simp [hz]

/-- The positive-paired diagonal is the continued prime--Gamma reciprocal-square sector
observable. -/
theorem ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector
    {z : ℂ} (hzim : z.im ≠ 0) :
    ccmPositivePairedReducedKernel z z =
      2 * (z.re / z.im) * (continuedPrimeArchReciprocalSquareTrace z).im := by
  have hz : z ≠ 0 := by
    intro h
    subst z
    exact hzim rfl
  simp only [ccmPositivePairedReducedKernel,
    continuedPrimeArchReciprocalSquareTrace, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.div_re, Complex.div_im, Complex.neg_re, Complex.neg_im,
    Complex.normSq, mul_re, mul_im]
  field_simp [hzim, hz]
  ring

/-- In the upper half-plane, nonnegativity of the paired diagonal is exactly the
reciprocal-square sector sign. -/
theorem ccmPositivePairedReducedKernel_self_nonneg_iff_re_mul_reciprocalSquare_im_nonneg
    {z : ℂ} (hzim : 0 < z.im) :
    0 ≤ ccmPositivePairedReducedKernel z z ↔
      0 ≤ z.re * (continuedPrimeArchReciprocalSquareTrace z).im := by
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim.ne']
  have hfactor : 0 < 2 / z.im := div_pos (by norm_num) hzim
  convert mul_nonneg_iff_of_pos_left hfactor using 1 <;> field_simp <;> ring

/-- Moment-germ form of the paired-diagonal identity. -/
theorem ccmPositivePairedReducedKernel_self_eq_momentGermSector
    {z : ℂ} (hzim : z.im ≠ 0) :
    ccmPositivePairedReducedKernel z z =
      2 * (z.re / z.im) * (normalizedPrimeArchMomentGerm z).im := by
  have hz : z ≠ 0 := by
    intro h
    subst z
    exact hzim rfl
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim,
    continuedPrimeArchReciprocalSquareTrace_eq_normalizedPrimeArchMomentGerm hz]

end


end RHTower
