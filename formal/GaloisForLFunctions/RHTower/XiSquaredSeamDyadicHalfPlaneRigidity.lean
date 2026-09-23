import GaloisForLFunctions.HTGeometry.DyadicHalfPlaneRigidity
import GaloisForLFunctions.RHTower.XiOrderFifteenCornerSourceExclusion

/-!
# Squared-Xi dyadic half-plane rigidity

All dyadic powers of one fixed shifted squared-Xi reciprocal coordinate lie in the closed right
half-plane exactly under RH.  Generic dyadic phase rigidity turns those infinitely sparse signs
into reality of each centered Xi spectral point.  The existing order-sixteen source theorem
unconditionally supplies the rung `k = 4`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Positive radial part of the squared-Xi reciprocal coordinate at fixed shift `y = 1`. -/
def xiSquaredSeamOneRadialA (q : XiZeroCopy) : ℝ :=
  (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + 1

/-- Transverse part of every shifted squared-Xi reciprocal coordinate. -/
def xiSquaredSeamTransverseB (q : XiZeroCopy) : ℝ :=
  2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im

/-- Squared-Xi reciprocal coordinate at the single fixed squared shift `y = 1`. -/
def xiSquaredSeamOneCoordinate (q : XiZeroCopy) : ℂ :=
  (((xiSquaredSeamOneRadialA q : ℝ) : ℂ) -
    xiSquaredSeamTransverseB q * I)⁻¹

/-- Every dyadic power of every fixed-shift squared-Xi coordinate lies in the closed right
half-plane. -/
def XiSquaredSeamDyadicHalfPlane : Prop :=
  ∀ q : XiZeroCopy,
    GaloisForLFunctions.ComplexDyadicHalfPlane (xiSquaredSeamOneCoordinate q)

theorem xiSquaredSeamOneRadialA_pos (q : XiZeroCopy) :
    0 < xiSquaredSeamOneRadialA q := by
  have hu : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 :=
    xi_divisor_support_centered_re_sq_lt_quarter q.1
  dsimp only [xiSquaredSeamOneRadialA]
  nlinarith [sq_nonneg (q.1 : ℂ).im]

theorem xiSquaredSeamOneCoordinate_im_formula (q : XiZeroCopy) :
    (xiSquaredSeamOneCoordinate q).im =
      xiSquaredSeamTransverseB q /
        (xiSquaredSeamOneRadialA q ^ (2 : ℕ) + xiSquaredSeamTransverseB q ^ (2 : ℕ)) := by
  rw [xiSquaredSeamOneCoordinate, Complex.inv_im, Complex.normSq_apply]
  norm_num [Complex.mul_re, Complex.mul_im]
  ring

/-- Dyadic half-plane signs force reality of every centered Xi spectral point and hence RH. -/
theorem riemannHypothesis_of_xiSquaredSeamDyadicHalfPlane
    (h : XiSquaredSeamDyadicHalfPlane) : RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hphase :=
    (GaloisForLFunctions.complexDyadicHalfPlane_iff_nonnegativeReal
      (xiSquaredSeamOneCoordinate q)).mp (h q)
  have him := hphase.1
  rw [xiSquaredSeamOneCoordinate_im_formula] at him
  have hA := xiSquaredSeamOneRadialA_pos q
  have hden : 0 < xiSquaredSeamOneRadialA q ^ (2 : ℕ) + xiSquaredSeamTransverseB q ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg (xiSquaredSeamTransverseB q)]
  have hB : xiSquaredSeamTransverseB q = 0 := by
    field_simp [hden.ne'] at him
    simpa using him
  have hgamma : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hdelta : (q.1 : ℂ).re - 1 / 2 = 0 := by
    have hprod : ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im = 0 := by
      dsimp only [xiSquaredSeamTransverseB] at hB
      nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right hgamma
  have hre : (q.1 : ℂ).re = 1 / 2 := by linarith
  have himsp : (xiSpectralPoint q).im = 0 := by
    rw [xiSpectralPoint_im_eq, hre]
    norm_num
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using himsp

/-- RH puts every fixed-shift coordinate on the positive real ray, so all dyadic signs hold. -/
theorem xiSquaredSeamDyadicHalfPlane_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiSquaredSeamDyadicHalfPlane := by
  intro q
  apply (GaloisForLFunctions.complexDyadicHalfPlane_iff_nonnegativeReal
    (xiSquaredSeamOneCoordinate q)).mpr
  have hre := xi_divisor_support_re_eq_half_of_rh hRH q.1
  constructor
  · simp [xiSquaredSeamOneCoordinate, xiSquaredSeamTransverseB, hre]
  · simp [xiSquaredSeamOneCoordinate, xiSquaredSeamOneRadialA,
      xiSquaredSeamTransverseB, hre, Complex.inv_re, Complex.normSq_apply]
    have hpowRe : ((((q.1 : ℂ).im : ℝ) : ℂ) ^ (2 : ℕ)).re = (q.1 : ℂ).im ^ (2 : ℕ) := by
      exact congrArg Complex.re (Complex.ofReal_pow (q.1 : ℂ).im 2).symm
    have hpowIm : ((((q.1 : ℂ).im : ℝ) : ℂ) ^ (2 : ℕ)).im = 0 := by
      exact congrArg Complex.im (Complex.ofReal_pow (q.1 : ℂ).im 2).symm
    rw [hpowRe, hpowIm]
    positivity

/-- **Squared-Xi dyadic half-plane RH law.** -/
theorem xiSquaredSeamDyadicHalfPlane_iff_riemannHypothesis :
    XiSquaredSeamDyadicHalfPlane ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_xiSquaredSeamDyadicHalfPlane,
    xiSquaredSeamDyadicHalfPlane_of_riemannHypothesis⟩

/-- The existing order-sixteen source theorem unconditionally supplies dyadic rung `k = 4`. -/
theorem xiSquaredSeamDyadic_rung_four_pos (q : XiZeroCopy) :
    0 < ((xiSquaredSeamOneCoordinate q) ^ (2 ^ (4 : ℕ))).re := by
  have h := xiOrderSixteenReciprocalPower_re_pos q (y := 1) (by norm_num)
  simpa [xiSquaredSeamOneCoordinate, xiSquaredSeamOneRadialA,
    xiSquaredSeamTransverseB] using h

end


end RHTower
