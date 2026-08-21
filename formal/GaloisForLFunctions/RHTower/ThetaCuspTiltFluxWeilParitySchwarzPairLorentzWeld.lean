import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParitySchwarzPairCrossing
import GaloisForLFunctions.RHTower.XiSourceEntropyCauchyTomography
import GaloisForLFunctions.RHTower.ScaleCovariantXiTransverseDefectBound
import GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceEntropyBoundaryWeld

/-!
# Lorentz decomposition of Schwarz-pair crossing and source-normal charge

The first Schwarz-pair Krein crossing is tangential in the rotated centered Xi plane.  Its
multiplicity-normalized speed is therefore not the square root of the RH-bearing transverse
defect.  This file identifies the exact complementary pair.

For `a = xiSpectralPoint q` and `lambda = a⁻²`, the tangential crossing rate and the
source-normal entropy rate satisfy

`T(q)² = 2 (|lambda| + Re lambda)`,

`N(q)² = 2 (|lambda| - Re lambda)`,

and hence `T(q)² + N(q)² = 4 / |a|²`.  Analytic multiplicity scales both channels without
changing the decomposition.  The actual continued-source crossing limit is `-m T(q)`, which is
strictly negative at every Xi zero in the interior source chamber.  In contrast, `m N(q)`
vanishes globally exactly when RH holds.

This is a formal route separation: tangential crossing magnitude alone cannot close RH, because
it is never zero.  Any producer must annihilate the orthogonal source-normal channel, equivalently
the conserved source entropy/transverse defect.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Multiplicity-free speed of the canonical tangential Schwarz-pair crossing. -/
def xiSchwarzPairTangentialCrossingRate (q : XiZeroCopy) : ℝ :=
  2 * |(xiSpectralPoint q).re| / Complex.normSq (xiSpectralPoint q)

/-- Source-normal rate, written using the actual reflected prime-tail entropy. -/
def xiSchwarzPairSourceNormalRate (q : XiZeroCopy) : ℝ :=
  |riemannReflectedSourceEntropy (q.1 : ℂ)| /
    Complex.normSq (xiSpectralPoint q)

/-- Analytic Xi multiplicity as a real scaling factor. -/
def xiSchwarzPairAnalyticMultiplicity (q : XiZeroCopy) : ℝ :=
  (((analyticOrderAt xi (q.1 : ℂ)).toNat : ℕ) : ℝ)

/-- Actual signed coefficient in the canonical tangential crossing limit. -/
def xiSchwarzPairTangentialCrossingCoefficient (q : XiZeroCopy) : ℝ :=
  -xiSchwarzPairAnalyticMultiplicity q * xiSchwarzPairTangentialCrossingRate q

/-- Multiplicity-weighted source-normal coefficient complementary to the crossing coefficient. -/
def xiSchwarzPairSourceNormalCoefficient (q : XiZeroCopy) : ℝ :=
  xiSchwarzPairAnalyticMultiplicity q * xiSchwarzPairSourceNormalRate q

/-- Norm of the reciprocal-square coordinate in centered spectral variables. -/
theorem norm_xiZeroCopyReciprocalSquare_eq_spectral (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ =
      (Complex.normSq (xiSpectralPoint q))⁻¹ := by
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow, Complex.sq_norm]

/-- Real part of the reciprocal-square coordinate in rotated tangent/normal variables. -/
theorem xiZeroCopyReciprocalSquare_re_eq_spectral (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).re =
      ((xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2) /
        Complex.normSq (xiSpectralPoint q) ^ 2 := by
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [xiZeroCopyReciprocalSquare, pow_two, Complex.mul_re,
    Complex.inv_re, Complex.inv_im]
  field_simp [hD]

/-- Tangential crossing rate is the positive longitudinal half of reciprocal-square energy. -/
theorem xiSchwarzPairTangentialCrossingRate_sq (q : XiZeroCopy) :
    xiSchwarzPairTangentialCrossingRate q ^ 2 =
      2 * (‖xiZeroCopyReciprocalSquare q‖ +
        (xiZeroCopyReciprocalSquare q).re) := by
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [xiSchwarzPairTangentialCrossingRate,
    norm_xiZeroCopyReciprocalSquare_eq_spectral,
    xiZeroCopyReciprocalSquare_re_eq_spectral]
  rw [div_pow, mul_pow, sq_abs]
  rw [Complex.normSq_apply]
  field_simp [hD]
  ring

/-- Prime-tail entropy is exactly twice normal displacement in the rotated Xi plane. -/
theorem xiSchwarzPairSourceNormalRate_eq (q : XiZeroCopy) :
    xiSchwarzPairSourceNormalRate q =
      2 * |(xiSpectralPoint q).im| /
        Complex.normSq (xiSpectralPoint q) := by
  rw [xiSchwarzPairSourceNormalRate,
    riemannReflectedSourceEntropy_xiZeroCopy_eq_two_spectralIm,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Source-normal rate is exactly the square root of twice the RH-bearing transverse defect. -/
theorem xiSchwarzPairSourceNormalRate_sq (q : XiZeroCopy) :
    xiSchwarzPairSourceNormalRate q ^ 2 =
      2 * HTGeometry.transverseDefect (xiZeroCopyReciprocalSquare q) := by
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [xiSchwarzPairSourceNormalRate_eq, HTGeometry.transverseDefect,
    norm_xiZeroCopyReciprocalSquare_eq_spectral,
    xiZeroCopyReciprocalSquare_re_eq_spectral]
  rw [div_pow, mul_pow, sq_abs]
  rw [Complex.normSq_apply]
  field_simp [hD]
  ring

/-- Exact Lorentz/Pythagorean conservation between tangential and source-normal rates. -/
theorem xiSchwarzPairLorentzPythagoras (q : XiZeroCopy) :
    xiSchwarzPairTangentialCrossingRate q ^ 2 +
        xiSchwarzPairSourceNormalRate q ^ 2 =
      4 / Complex.normSq (xiSpectralPoint q) := by
  rw [xiSchwarzPairTangentialCrossingRate_sq,
    xiSchwarzPairSourceNormalRate_sq, HTGeometry.transverseDefect,
    norm_xiZeroCopyReciprocalSquare_eq_spectral]
  ring

/-- Tangential crossing rate is strictly positive at every Xi divisor copy. -/
theorem xiSchwarzPairTangentialCrossingRate_pos (q : XiZeroCopy) :
    0 < xiSchwarzPairTangentialCrossingRate q := by
  rw [xiSchwarzPairTangentialCrossingRate]
  apply div_pos
  · apply mul_pos (by norm_num)
    rw [abs_pos, xiSpectralPoint_re_eq]
    exact xi_divisor_support_im_ne_zero q.1
  · exact Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)

/-- Source-normal rate vanishes exactly on the critical line. -/
theorem xiSchwarzPairSourceNormalRate_eq_zero_iff (q : XiZeroCopy) :
    xiSchwarzPairSourceNormalRate q = 0 ↔ (xiSpectralPoint q).im = 0 := by
  rw [xiSchwarzPairSourceNormalRate_eq]
  have hD : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
    (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
  rw [div_eq_zero_iff]
  simp [hD]

/-- Global source-normal rate vanishing is exactly RH. -/
theorem forall_xiSchwarzPairSourceNormalRate_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, xiSchwarzPairSourceNormalRate q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply xiSpectralPoint_im_eq_zero_iff_rh.mpr
    intro q
    exact (xiSchwarzPairSourceNormalRate_eq_zero_iff q).mp (h q)
  · intro h q
    apply (xiSchwarzPairSourceNormalRate_eq_zero_iff q).mpr
    exact xiSpectralPoint_im_eq_zero_iff_rh.mp h q

/-- Multiplicity-weighted crossing square is longitudinal reciprocal-square energy. -/
theorem xiSchwarzPairTangentialCrossingCoefficient_sq (q : XiZeroCopy) :
    xiSchwarzPairTangentialCrossingCoefficient q ^ 2 =
      2 * xiSchwarzPairAnalyticMultiplicity q ^ 2 *
        (‖xiZeroCopyReciprocalSquare q‖ +
          (xiZeroCopyReciprocalSquare q).re) := by
  rw [xiSchwarzPairTangentialCrossingCoefficient,
    mul_pow, neg_sq, xiSchwarzPairTangentialCrossingRate_sq]
  ring

/-- Multiplicity-weighted normal square is the RH-bearing transverse energy. -/
theorem xiSchwarzPairSourceNormalCoefficient_sq (q : XiZeroCopy) :
    xiSchwarzPairSourceNormalCoefficient q ^ 2 =
      2 * xiSchwarzPairAnalyticMultiplicity q ^ 2 *
        HTGeometry.transverseDefect (xiZeroCopyReciprocalSquare q) := by
  rw [xiSchwarzPairSourceNormalCoefficient, mul_pow,
    xiSchwarzPairSourceNormalRate_sq]
  ring

/-- Analytic multiplicity is strictly positive on every Xi divisor copy. -/
theorem xiSchwarzPairAnalyticMultiplicity_pos (q : XiZeroCopy) :
    0 < xiSchwarzPairAnalyticMultiplicity q := by
  have hmNat : 0 < (analyticOrderAt xi (q.1 : ℂ)).toNat :=
    Nat.pos_of_ne_zero
      (xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support q.1))
  rw [xiSchwarzPairAnalyticMultiplicity]
  exact_mod_cast hmNat

/-- Tangential coefficient is always strictly negative, so its vanishing cannot encode RH. -/
theorem xiSchwarzPairTangentialCrossingCoefficient_neg (q : XiZeroCopy) :
    xiSchwarzPairTangentialCrossingCoefficient q < 0 := by
  rw [xiSchwarzPairTangentialCrossingCoefficient]
  exact mul_neg_of_neg_of_pos
    (neg_neg_of_pos (xiSchwarzPairAnalyticMultiplicity_pos q))
    (xiSchwarzPairTangentialCrossingRate_pos q)

/-- Multiplicity does not change the critical-line zero fibre of the normal channel. -/
theorem xiSchwarzPairSourceNormalCoefficient_eq_zero_iff (q : XiZeroCopy) :
    xiSchwarzPairSourceNormalCoefficient q = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  rw [xiSchwarzPairSourceNormalCoefficient, mul_eq_zero]
  have hm : xiSchwarzPairAnalyticMultiplicity q ≠ 0 :=
    ne_of_gt (xiSchwarzPairAnalyticMultiplicity_pos q)
  simp [hm, xiSchwarzPairSourceNormalRate_eq_zero_iff]

/-- Global multiplicity-weighted source-normal coefficient vanishing is exactly RH. -/
theorem forall_xiSchwarzPairSourceNormalCoefficient_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, xiSchwarzPairSourceNormalCoefficient q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply forall_xiSchwarzPairSourceNormalRate_eq_zero_iff_riemannHypothesis.mp
    intro q
    exact (xiSchwarzPairSourceNormalRate_eq_zero_iff q).mpr
      ((xiSchwarzPairSourceNormalCoefficient_eq_zero_iff q).mp (h q))
  · intro h q
    exact (xiSchwarzPairSourceNormalCoefficient_eq_zero_iff q).mpr
      (xiSpectralPoint_im_eq_zero_iff_rh.mp h q)

/-- Analytic multiplicity preserves the exact tangent/normal Pythagorean conservation law. -/
theorem xiSchwarzPairCoefficientPythagoras (q : XiZeroCopy) :
    xiSchwarzPairTangentialCrossingCoefficient q ^ 2 +
        xiSchwarzPairSourceNormalCoefficient q ^ 2 =
      4 * xiSchwarzPairAnalyticMultiplicity q ^ 2 /
        Complex.normSq (xiSpectralPoint q) := by
  rw [xiSchwarzPairTangentialCrossingCoefficient,
    xiSchwarzPairSourceNormalCoefficient, mul_pow, mul_pow, neg_sq]
  calc
    xiSchwarzPairAnalyticMultiplicity q ^ 2 *
          xiSchwarzPairTangentialCrossingRate q ^ 2 +
        xiSchwarzPairAnalyticMultiplicity q ^ 2 *
          xiSchwarzPairSourceNormalRate q ^ 2 =
        xiSchwarzPairAnalyticMultiplicity q ^ 2 *
          (xiSchwarzPairTangentialCrossingRate q ^ 2 +
            xiSchwarzPairSourceNormalRate q ^ 2) := by ring
    _ = xiSchwarzPairAnalyticMultiplicity q ^ 2 *
        (4 / Complex.normSq (xiSpectralPoint q)) := by
      rw [xiSchwarzPairLorentzPythagoras]
    _ = 4 * xiSchwarzPairAnalyticMultiplicity q ^ 2 /
        Complex.normSq (xiSpectralPoint q) := by ring

/-- The abstract crossing limit specializes to the actual Xi divisor and equals the tangential,
not source-normal, coefficient. -/
theorem tendsto_ccmPositivePairedReducedKernel_xiZeroCopy_tangentialCrossing
    (q : XiZeroCopy) (him : 0 < (xiSpectralPoint q).im) :
    Tendsto
      (fun n => xiReciprocalSquareTransverseStep n *
        ccmPositivePairedReducedKernel
          (xiReciprocalSquareTransverseApproach (xiSpectralPoint q) n)
          (xiReciprocalSquareTransverseApproach (xiSpectralPoint q) n))
      atTop
      (nhds (xiSchwarzPairTangentialCrossingCoefficient q)) := by
  have himhalf : (xiSpectralPoint q).im < 1 / 2 :=
    (xiSpectralPoint_im_mem_openHalf q).2
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    rw [xiSpectralPoint_re_eq]
    exact xi_divisor_support_im_ne_zero q.1
  have hXi : XiC (xiSpectralPoint q) = 0 := XiC_xiSpectralPoint_eq_zero q
  have hlim := tendsto_ccmPositivePairedReducedKernel_transverse_crossing
    him himhalf hre hXi
  convert hlim using 1
  have hcoord : (1 / 2 : ℂ) + xiSpectralPoint q * I = (q.1 : ℂ) := by
    rw [xiSpectralPoint]
    calc
      (1 / 2 : ℂ) + (((q.1 : ℂ) - 1 / 2) * -I) * I =
          1 / 2 + ((q.1 : ℂ) - 1 / 2) * ((-I) * I) := by ring
      _ = 1 / 2 + ((q.1 : ℂ) - 1 / 2) := by
        rw [neg_mul, I_mul_I]
        ring
      _ = (q.1 : ℂ) := by ring
  rw [xiSchwarzPairTangentialCrossingCoefficient,
    xiSchwarzPairAnalyticMultiplicity, xiSchwarzPairTangentialCrossingRate,
    hcoord]
  ring

end

end RHTower
