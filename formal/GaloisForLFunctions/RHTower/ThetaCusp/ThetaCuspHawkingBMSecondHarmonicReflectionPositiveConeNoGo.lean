import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicCarrierNormalizedReflectionObstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTotalRenormalizedAngularPeriod

/-!
# Positive-cone no-go for reflected BM radial-current cancellation

On every Xi fibre, both canonical complementary exponents in a functional-equation reflection
pair have strictly positive real part.  Therefore no nontrivial pair of nonnegative real source
weights can cancel their exact regular/complementary radial currents.  The positive cone meets the
reflection-cancellation hyperplane only at its vertex.

Consequently a nonzero functional-equation-odd physical Peierls seam cannot be produced by
Hermitian norm-square weights alone.  It requires genuinely complex or sign-indefinite orientation
from global retarded/advanced source incidence.

`[NEW] [NO-GO] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Canonical BM complementary exponent lies in the open right half-plane on every Xi fibre. -/
theorem d4BMXiPlusPlusComplementaryFrobeniusExponent_re_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < (d4BMPlusPlusComplementaryFrobeniusExponent n
      (d4BMXiMixedHorizonAngularMomentum q)).re := by
  rw [d4BMPlusPlusComplementaryFrobeniusExponent_eq]
  have him := d4BMXiMixedHorizonAngularMomentum_im_mem_openHalf q
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  norm_num [Complex.mul_re]
  linarith

/-- Nonnegative real combination of canonical currents on a reflected Xi pair. -/
def d4BMXiReflectionPositiveConeRegularComplementaryCurrent
    (n : ℕ) (q : XiZeroCopy) (a b : NNReal) : ℂ :=
  ((a : ℝ) : ℂ) * d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
      (d4BMXiMixedHorizonAngularMomentum q) (1 / 2) +
    ((b : ℝ) : ℂ) * d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue n
      (d4BMXiMixedHorizonAngularMomentum (xiZeroCopyReflectEquiv q)) (1 / 2)

/-- Positive-cone rigidity: reflected canonical currents cancel only at zero source weight. -/
theorem d4BMXiReflectionPositiveConeRegularComplementaryCurrent_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) (a b : NNReal) :
    d4BMXiReflectionPositiveConeRegularComplementaryCurrent n q a b = 0 ↔
      a = 0 ∧ b = 0 := by
  have hz0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hz1 : (1 / 2 : ℝ) < 1 := by norm_num
  rw [d4BMXiReflectionPositiveConeRegularComplementaryCurrent,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz0 hz1,
    d4BMSecondHarmonicRegularComplementaryPolarizedCurrentValue_eq_negExponent n
      (d4BMXiMixedHorizonAngularMomentum (xiZeroCopyReflectEquiv q))
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero (xiZeroCopyReflectEquiv q)) hz0 hz1]
  constructor
  · intro h
    by_contra hab
    have hne : a ≠ 0 ∨ b ≠ 0 := by
      simpa only [not_and_or] using hab
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
    have hp := d4BMXiPlusPlusComplementaryFrobeniusExponent_re_pos n q
    have hpr := d4BMXiPlusPlusComplementaryFrobeniusExponent_re_pos n
      (xiZeroCopyReflectEquiv q)
    rcases hne with ha | hb
    · have hane : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      have hapos : 0 < (a : ℝ) := lt_of_le_of_ne a.2 (Ne.symm hane)
      have hbnonneg : 0 ≤ (b : ℝ) := b.2
      nlinarith [mul_pos hapos hp, mul_nonneg hbnonneg hpr.le]
    · have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      have hbpos : 0 < (b : ℝ) := lt_of_le_of_ne b.2 (Ne.symm hbne)
      have hanonneg : 0 ≤ (a : ℝ) := a.2
      nlinarith [mul_pos hbpos hpr, mul_nonneg hanonneg hp.le]
  · rintro ⟨rfl, rfl⟩
    simp

end

end RHTower
