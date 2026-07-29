import GaloisForLFunctions.RHTower.DeningerArithmeticLocalHodgeObstruction
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse

/-!
# Purity curvature exponentiates to the FE--Schwarz prime seam

The coefficient of the exact Deninger local-Hodge commutator and the finite
FE--Schwarz prime seam are two realizations of one weight-one purity curvature.
The former is infinitesimal; the latter is its exponential transgression at a
positive scale.

This bridge is unconditional.  It does not assert that the curvature vanishes.
-/

open Complex

namespace RHTower

noncomputable section

/-- Weight-one failure of a complex spectral point to be centered-unitary. -/
def weightOnePurityCurvature (rho : ℂ) : ℂ :=
  1 - rho - starRingEnd ℂ rho

/--
The FE--Schwarz seam is the exponential transgression of weight-one purity
curvature.  The prefactor is nonzero at every scale greater than one, so the
transgression introduces no additional zero.
-/
theorem orbitwiseScaleSeamCharge_eq_purityCurvatureTransgression
    {x : ℝ} (hx : 0 < x) (rho : ℂ) :
    orbitwiseScaleSeamCharge x rho =
      (Real.log x : ℂ) * (x : ℂ) ^ (-(1 - rho)) *
        ((x : ℂ) ^ weightOnePurityCurvature rho - 1) := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hx
  have hexponent :
      -(starRingEnd ℂ rho) =
        -(1 - rho) + weightOnePurityCurvature rho := by
    simp only [weightOnePurityCurvature]
    ring
  rw [orbitwiseScaleSeamCharge, hexponent,
    Complex.cpow_add _ _ hxC]
  ring

/--
The coefficient of the Deninger local-Hodge commutator is the same
weight-one purity curvature evaluated at the uncentered Xi divisor point.
-/
theorem deningerLocalHodgeCoefficient_eq_weightOnePurityCurvature
    (q : XiZeroCopy) :
    1 -
        (1 / 2 + Complex.I * xiSpectralPointSupport q.1) -
        starRingEnd ℂ
          (1 / 2 + Complex.I * xiSpectralPointSupport q.1) =
      weightOnePurityCurvature (q.1 : ℂ) := by
  have hlambda :
      1 / 2 + Complex.I * xiSpectralPointSupport q.1 =
        (q.1 : ℂ) := by
    simp only [xiSpectralPointSupport]
    have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
      rw [mul_neg, Complex.I_mul_I]
      ring
    calc
      1 / 2 + Complex.I * (((q.1 : ℂ) - 1 / 2) * -Complex.I) =
          1 / 2 + ((q.1 : ℂ) - 1 / 2) *
            (Complex.I * -Complex.I) := by ring
      _ = (q.1 : ℂ) := by rw [hI]; ring
  rw [hlambda]
  rfl

/--
The actual local Hodge obstruction, rewritten with exactly the curvature whose
finite-scale transgression is the FE--Schwarz prime seam.
-/
theorem deningerCompactOpenLocalJetHodge_theta_defect_eq_purityCurvature
    (q : XiZeroCopy)
    (x : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenThetaCompact
          (deningerCompactOpenLocalJetHodge q.1 x) -
        deningerCompactOpenLocalJetHodge q.1
          (deningerCompactOpenTheta x) =
      weightOnePurityCurvature (q.1 : ℂ) •
        deningerCompactOpenLocalJetHodge q.1 x := by
  rw [deningerCompactOpenLocalJetHodge_theta_defect,
    deningerLocalHodgeCoefficient_eq_weightOnePurityCurvature]

end

end RHTower
