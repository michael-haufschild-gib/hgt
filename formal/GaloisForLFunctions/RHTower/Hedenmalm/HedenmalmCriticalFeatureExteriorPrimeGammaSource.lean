import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmOrientedAdjacentTransverseDeterminantQuantum
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureHolomorphicSectorCoercivity

/-!
# Exterior-square prime--Gamma source of critical features

Every entry of the real-centered critical-feature Weil matrix has an explicit four-term
absolute-Euler prime--Gamma formula.  This module packages those formulas into the exact
exterior determinant.  The resulting source matrix and determinant are real and symmetric
unconditionally, despite being defined by complex source cups.

This identifies the arithmetic exterior-square observable required by the transverse determinant
quantum.  A quantitative dyadic bound for its height-dephased four-leg trace remains separate.
-/

open Complex

namespace RHTower

noncomputable section

/-- Explicit four-term absolute-Euler prime--Gamma polarization of two critical features. -/
def criticalFeaturePrimeGammaSourcePolarization (t s : ℝ) : ℂ :=
  criticalHardyLowerLowerPrimeArchSource t s +
    criticalHardyPrimeGammaSourceCup t s +
    (starRingEnd ℂ) (criticalHardyPrimeGammaSourceCup s t) +
    criticalHardyUpperUpperPrimeArchSource t s

/-- Source polarization is exactly the multiplicity-exact Xi Weil polarization. -/
theorem criticalFeaturePrimeGammaSourcePolarization_eq_weil (t s : ℝ) :
    criticalFeaturePrimeGammaSourcePolarization t s =
      xiWeilPolarization
        (criticalFeatureCauchyKernelTest t)
        (criticalFeatureCauchyKernelTest s) := by
  rw [criticalFeaturePrimeGammaSourcePolarization]
  exact (xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_primeGammaSource t s).symm

/-- Real critical features make the complete source polarization symmetric. -/
theorem criticalFeaturePrimeGammaSourcePolarization_symm (t s : ℝ) :
    criticalFeaturePrimeGammaSourcePolarization t s =
      criticalFeaturePrimeGammaSourcePolarization s t := by
  rw [criticalFeaturePrimeGammaSourcePolarization_eq_weil,
    criticalFeaturePrimeGammaSourcePolarization_eq_weil]
  unfold xiWeilPolarization
  rw [xiWeilSharp_criticalFeatureCauchyKernelTest,
    xiWeilSharp_criticalFeatureCauchyKernelTest]
  apply tsum_congr
  intro q
  ring

/-- The explicit prime--Gamma source polarization is fixed by complex conjugation. -/
theorem conj_criticalFeaturePrimeGammaSourcePolarization (t s : ℝ) :
    (starRingEnd ℂ) (criticalFeaturePrimeGammaSourcePolarization t s) =
      criticalFeaturePrimeGammaSourcePolarization t s := by
  calc
    (starRingEnd ℂ) (criticalFeaturePrimeGammaSourcePolarization t s) =
        (starRingEnd ℂ) (xiWeilPolarization
          (criticalFeatureCauchyKernelTest t)
          (criticalFeatureCauchyKernelTest s)) := by
      rw [criticalFeaturePrimeGammaSourcePolarization_eq_weil]
    _ = xiWeilPolarization
          (criticalFeatureCauchyKernelTest s)
          (criticalFeatureCauchyKernelTest t) :=
      (xiWeilPolarization_conj_symm _ _).symm
    _ = criticalFeaturePrimeGammaSourcePolarization s t := by
      rw [criticalFeaturePrimeGammaSourcePolarization_eq_weil]
    _ = criticalFeaturePrimeGammaSourcePolarization t s :=
      criticalFeaturePrimeGammaSourcePolarization_symm s t

theorem criticalFeaturePrimeGammaSourcePolarization_im (t s : ℝ) :
    (criticalFeaturePrimeGammaSourcePolarization t s).im = 0 := by
  have h := congrArg Complex.im
    (conj_criticalFeaturePrimeGammaSourcePolarization t s)
  simp only [Complex.conj_im] at h
  linarith

/-- Arithmetic exterior determinant of the two-feature prime--Gamma source matrix. -/
def criticalFeaturePrimeGammaExteriorDet (t s : ℝ) : ℂ :=
  criticalFeaturePrimeGammaSourcePolarization t t *
      criticalFeaturePrimeGammaSourcePolarization s s -
    criticalFeaturePrimeGammaSourcePolarization t s *
      criticalFeaturePrimeGammaSourcePolarization s t

/-- Exact Weil-form interpretation of the arithmetic source determinant. -/
theorem criticalFeaturePrimeGammaExteriorDet_eq_weil (t s : ℝ) :
    criticalFeaturePrimeGammaExteriorDet t s =
      xiWeilPolarization
          (criticalFeatureCauchyKernelTest t)
          (criticalFeatureCauchyKernelTest t) *
        xiWeilPolarization
          (criticalFeatureCauchyKernelTest s)
          (criticalFeatureCauchyKernelTest s) -
      xiWeilPolarization
          (criticalFeatureCauchyKernelTest t)
          (criticalFeatureCauchyKernelTest s) *
        xiWeilPolarization
          (criticalFeatureCauchyKernelTest s)
          (criticalFeatureCauchyKernelTest t) := by
  simp only [criticalFeaturePrimeGammaExteriorDet,
    criticalFeaturePrimeGammaSourcePolarization_eq_weil]

/-- The explicit exterior prime--Gamma determinant is real unconditionally. -/
theorem criticalFeaturePrimeGammaExteriorDet_im (t s : ℝ) :
    (criticalFeaturePrimeGammaExteriorDet t s).im = 0 := by
  rw [criticalFeaturePrimeGammaExteriorDet, Complex.sub_im, Complex.mul_im,
    Complex.mul_im]
  rw [criticalFeaturePrimeGammaSourcePolarization_im,
    criticalFeaturePrimeGammaSourcePolarization_im,
    criticalFeaturePrimeGammaSourcePolarization_im,
    criticalFeaturePrimeGammaSourcePolarization_im]
  ring

end

end RHTower
