import GaloisForLFunctions.RHTower.FrankensteinXiBidirectionalIntegralCartierSource
import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent

/-!
# Integral Cartier descent as literal bilateral source admission

The integral bidirectional conormal is welded here to two analytic source carriers without
passing through the incompatible centered-monodromy import branch: the full geometric
source-formation history and the derivative-free Gamma-six determinant current.

Local smoothness does not detect horizontal grade.  Exact detection is bilateral and cofinal:
both reflected formation histories, equivalently the ordinary-prime determinant current, are
summable precisely when the integral Gamma reporter descends.
-/

open Complex

namespace RHTower

noncomputable section

/-- Integral Cartier descent is exactly bilateral admission of the full literal source-formation
history.  Pointwise smoothness is insufficient: both cofinal orientations must be summable. -/
theorem xiBidirectionalIntegralGammaReporter_iff_bilateralFormationAdmission
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      (Summable (GaloisForLFunctions.HTGeometry.geometricRefinementEnergy
          (Real.exp (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho))) ∧
        Summable (GaloisForLFunctions.HTGeometry.geometricRefinementEnergy
          (Real.exp (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho))⁻¹)) := by
  rw [deningerXiBidirectionalIntegralGammaReporter_nonempty_iff,
    sourceHorizontalGammaSix_bilateralFormationAdmission_iff_det_eq_zero,
    det_sourceHorizontalGammaSixCurvedSuspension, Complex.ofReal_eq_zero,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or, primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Integral Cartier descent is exactly summability of the literal, derivative-free Gamma-six
determinant current.  This retains the Xi multiplicity copy and every ordinary-prime label. -/
theorem xiBidirectionalIntegralGammaReporter_iff_summable_sourceDeterminantCurrent
    {m : ℕ} (hm : 1 ≤ m) (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      Summable (gammaSixSuspensionDeterminantPrimeCurrent m (xiFirstZeroCopy rho)) := by
  rw [deningerXiBidirectionalIntegralGammaReporter_nonempty_iff,
    summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_centeredRate_eq_zero
      hm (xiFirstZeroCopy rho),
    xiFirstZeroCopy_fst, primeDepthBVWoldXiCenteredRate_eq_zero_iff]

end

end RHTower
