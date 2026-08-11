import GaloisForLFunctions.RHTower.HedenmalmThetaGreenSquareBoundaryLaw
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceEntropyBoundaryWeld
import GaloisForLFunctions.RHTower.RouteRBurnolThetaSameFiberOrientation

/-!
# Reflected-pair Green-boundary cancellation is unconditional

Functional-equation reflection negates the centered theta spectral coordinate and preserves the
source root energy.  Hence it negates the signed rank-two boundary flux copy by copy.  Cancellation
after pairing reflected divisor fibres is therefore automatic and cannot be a Route P producer;
the RH-strength condition remains neutrality on each individual fibre.
-/

open Complex

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Reflected-pair neutrality only asks for cancellation after the two functional-equation fibres
have been aggregated. -/
def ThetaGreenReflectedPairNeutral : Prop :=
  ∀ q : XiZeroCopy,
    thetaXiRankTwoBoundaryFlux q +
      thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) = 0

/-- Functional-equation reflection preserves the positive theta root energy on every
multiplicity-exact divisor copy. -/
theorem thetaXiRootEnergy_reflect (q : XiZeroCopy) :
    thetaXiRootEnergy (xiZeroCopyReflectEquiv q) = thetaXiRootEnergy q := by
  change thetaRootEnergy (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
    thetaRootEnergy (xiSpectralPoint q)
  rw [xiSpectralPoint_reflect]
  exact thetaRootEnergy_neg_of_zero
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- **Reflection anti-current law.**  The signed Green-boundary flux on the reflected fibre is the
negative of the original flux. -/
theorem thetaXiRankTwoBoundaryFlux_reflect (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) =
      -thetaXiRankTwoBoundaryFlux q := by
  rw [thetaXiRankTwoBoundaryFlux_eq, thetaXiRankTwoBoundaryFlux_eq,
    xiSpectralPoint_reflect, thetaXiRootEnergy_reflect]
  simp

/-- Functional-equation reflection negates the nonzero eigenvalue of the unsquared theta source
inverse. -/
theorem thetaXiReciprocalEigenvalue_reflect (q : XiZeroCopy) :
    thetaXiReciprocalEigenvalue (xiZeroCopyReflectEquiv q) =
      -thetaXiReciprocalEigenvalue q := by
  rw [thetaXiReciprocalEigenvalue, thetaXiReciprocalEigenvalue,
    xiSpectralPoint_reflect]
  simp

/-- Squaring folds the two reflected source eigenvalues to the same Route P node. -/
theorem thetaXiReciprocalEigenvalue_sq_reflect (q : XiZeroCopy) :
    thetaXiReciprocalEigenvalue (xiZeroCopyReflectEquiv q) ^ 2 =
      thetaXiReciprocalEigenvalue q ^ 2 := by
  rw [thetaXiReciprocalEigenvalue_reflect]
  ring

/-- **Pointwise Route P criterion.**  On each oriented divisor fibre, its squared theta
eigenvalue is a strictly positive real number exactly when that fibre's Green-boundary current is
neutral. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    (∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero]
  constructor
  · rintro ⟨r, _hr, hsquare⟩
    have hnodeIm : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [← thetaXiReciprocalEigenvalue_sq_eq_reciprocalSquare, hsquare]
      simp
    rw [xiZeroCopyReciprocalSquare_im_eq_spectral] at hnodeIm
    have hnorm : Complex.normSq (xiSpectralPoint q) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)).ne'
    have hnegnum : -(2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im) = 0 :=
      (div_eq_zero_iff.mp hnodeIm).resolve_right hnorm
    have hnum : 2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im = 0 :=
      neg_eq_zero.mp hnegnum
    have hheight : 2 < (xiSpectralPoint q).re ^ 2 := by
      rw [xiSpectralPoint_re_eq]
      exact xiZeroCopy_two_lt_im_sq q
    have hre : (xiSpectralPoint q).re ≠ 0 := by
      nlinarith
    have him : (xiSpectralPoint q).im = 0 :=
      (mul_eq_zero.mp hnum).resolve_left
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hre)
    exact him
  · intro him
    refine ⟨(xiZeroCopyReciprocalSquare q).re,
      xiZeroCopyReciprocalSquare_re_pos q, ?_⟩
    rw [thetaXiReciprocalEigenvalue_sq_eq_reciprocalSquare]
    apply Complex.ext
    · simp
    · rw [xiZeroCopyReciprocalSquare_im_eq_spectral, him]
      simp

/-- Pairing functional-equation fibres cancels the rank-two Green current unconditionally. -/
theorem thetaGreenReflectedPairNeutral_unconditional :
    ThetaGreenReflectedPairNeutral := by
  intro q
  rw [thetaXiRankTwoBoundaryFlux_reflect]
  ring

/-- **Square-fold blindness.**  Both reflected divisor vectors are eigenvectors of `B²` at the
same squared node, while their aggregate Green-boundary current is zero unconditionally. -/
theorem thetaGreenSquaredReflectionFiber_sameNode_zeroCurrent (q : XiZeroCopy) :
    thetaCompactSourceInverse
        (thetaCompactSourceInverse (thetaXiDivisorEigenvector q)) =
        thetaXiReciprocalEigenvalue q ^ 2 • thetaXiDivisorEigenvector q ∧
      thetaCompactSourceInverse
        (thetaCompactSourceInverse
          (thetaXiDivisorEigenvector (xiZeroCopyReflectEquiv q))) =
        thetaXiReciprocalEigenvalue q ^ 2 •
          thetaXiDivisorEigenvector (xiZeroCopyReflectEquiv q) ∧
      thetaXiRankTwoBoundaryFlux q +
        thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) = 0 := by
  refine ⟨thetaCompactSourceInverse_sq_thetaXi_eigen q, ?_,
    thetaGreenReflectedPairNeutral_unconditional q⟩
  rw [← thetaXiReciprocalEigenvalue_sq_reflect]
  exact thetaCompactSourceInverse_sq_thetaXi_eigen (xiZeroCopyReflectEquiv q)

/-- Adding automatic reflected-pair cancellation does not weaken the genuine same-fibre boundary
condition: the conjunction is still exactly RH. -/
theorem thetaGreenReflectedPairNeutral_and_fiberNeutral_iff_riemannHypothesis :
    ThetaGreenReflectedPairNeutral ∧ ThetaGreenBoundaryNeutral ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact thetaGreenBoundaryNeutral_iff_riemannHypothesis.mp h.2
  · intro hRH
    exact ⟨thetaGreenReflectedPairNeutral_unconditional,
      thetaGreenBoundaryNeutral_iff_riemannHypothesis.mpr hRH⟩

end

end RHTower.HedenmalmThetaSource
