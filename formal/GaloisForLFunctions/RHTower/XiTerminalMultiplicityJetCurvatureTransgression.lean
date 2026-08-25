import GaloisForLFunctions.RHTower.FrankensteinGammaCompositionScaleZeroDescent
import GaloisForLFunctions.RHTower.XiNodalDefectSuperselection

/-!
# Terminal-multiplicity-jet transgression of Xi mixed curvature

The nodal master equation exposes one mixed horizontal-grade/vertical-phase curvature.  The
terminal theta-source multiplicity jet independently retains the first nonzero longitudinal
divisor coefficient.  This module proves that these are not merely parallel RH detectors: the
finite-cut logarithmic norm gain of the actual nonzero terminal jet measures the horizontal
factor of the mixed curvature exactly.

For a cut `x`, the gain is `x * (2 * Re rho - 1) / 2`.  At a nonzero cut, multiplying by the
vertical Xi phase reconstructs the complete second-order arithmetic descent defect.  Thus
multiplicity survives as a nonzero source coefficient while its cut holonomy is precisely the
curvature obstructing two-cell coherence.
-/

open Complex

namespace RHTower

noncomputable section

/-- The terminal multiplicity jet's norm ratio across one logarithmic cut.  The denominator is
nonzero for every Xi divisor support point. -/
def xiThetaTerminalMultiplicityCutLogGain
    (rho : XiDivisorSupport) (x : ℝ) : ℝ :=
  Real.log
    (‖xiThetaTerminalMultiplicityCutJet rho x‖ /
      ‖xiThetaTerminalMultiplicityCutJet rho 0‖)

/-- The finite-cut norm ratio is the exponential of one half of the centered horizontal rate.
The multiplicity-dependent terminal coefficient cancels but remains nonzero. -/
theorem norm_xiThetaTerminalMultiplicityCutJet_div_zero_eq_exp_centeredRate
    (rho : XiDivisorSupport) (x : ℝ) :
    ‖xiThetaTerminalMultiplicityCutJet rho x‖ /
        ‖xiThetaTerminalMultiplicityCutJet rho 0‖ =
      Real.exp (x * primeDepthBVWoldXiCenteredRate rho / 2) := by
  rw [norm_xiThetaTerminalMultiplicityCutJet_eq,
    norm_xiThetaTerminalMultiplicityCutJet_eq]
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  have hM : ‖∫ y : ℝ, thetaCuspFourierLaplaceJetIntegrand
      (xiSupportMultiplicity rho) (xiSpectralPointSupport rho) y‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact ((xiSupportMultiplicity_eq_iff_thetaCuspFourierLaplaceJet rho
      (xiSupportMultiplicity rho)).mp rfl).2
  rw [mul_div_cancel_right₀ _ hM]
  congr 1
  rw [xiSpectralPointSupport_im, primeDepthBVWoldXiCenteredRate]
  ring

/-- Exact terminal-jet holonomy law: cut log gain is horizontal modular charge integrated over
the cut, with the half-density factor `1/2`. -/
theorem xiThetaTerminalMultiplicityCutLogGain_eq
    (rho : XiDivisorSupport) (x : ℝ) :
    xiThetaTerminalMultiplicityCutLogGain rho x =
      x * primeDepthBVWoldXiCenteredRate rho / 2 := by
  rw [xiThetaTerminalMultiplicityCutLogGain,
    norm_xiThetaTerminalMultiplicityCutJet_div_zero_eq_exp_centeredRate,
    Real.log_exp]

/-- At a nontrivial cut, terminal-jet holonomy times vertical phase is exactly the mixed
grade--phase curvature coefficient. -/
theorem xiNodalMixedCurvature_eq_terminalMultiplicityCutLogGain
    (q : XiZeroCopy) {x : ℝ} (hx : x ≠ 0) :
    primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im =
      2 * (q.1 : ℂ).im / x *
        xiThetaTerminalMultiplicityCutLogGain q.1 x := by
  rw [xiThetaTerminalMultiplicityCutLogGain_eq]
  field_simp

/-- The complete covariant boundary of the arithmetic first-order anomaly is reconstructed from
the finite-cut log gain of the actual terminal multiplicity jet. -/
theorem xiNodalArithmeticSecondOrderDefect_apply_eq_terminalMultiplicityCutLogGain
    (q : XiZeroCopy) {cut : ℝ} (hcut : cut ≠ 0)
    (x : DeningerCalderonWittGlobalOrientedKoszulTotalCarrier) :
    GaloisForLFunctions.HTGeometry.secondOrderConstraintDescentDefect
        deningerCalderonWittGlobalOrientedKoszulTotalDifferential
        deningerCalderonWittNodalTopObservation
        (xiNodalTotalDefectEnd q) x =
      (((2 * (q.1 : ℂ).im / cut *
          xiThetaTerminalMultiplicityCutLogGain q.1 cut : ℝ) : ℂ)) •
        deningerCalderonWittNodalTopObservation x := by
  rw [xiNodalArithmeticSecondOrderDefect_apply]
  congr 1
  exact_mod_cast
    xiNodalMixedCurvature_eq_terminalMultiplicityCutLogGain q hcut

/-- One nonzero cut is enough: zero terminal-jet holonomy is exactly coherent second-order
descent.  This kills transverse curvature without killing the nonzero terminal multiplicity
coefficient itself. -/
theorem xiThetaTerminalMultiplicityCutLogGain_eq_zero_iff_nodalArithmeticSecondOrderCoherent
    (q : XiZeroCopy) {x : ℝ} (hx : x ≠ 0) :
    xiThetaTerminalMultiplicityCutLogGain q.1 x = 0 ↔
      XiNodalArithmeticSecondOrderCoherent q := by
  rw [xiThetaTerminalMultiplicityCutLogGain_eq,
    xiNodalArithmeticSecondOrderCoherent_iff,
    xiNodalDefectMasterEquation_iff_superselected,
    xiNodalDefectSuperselected_iff_re_eq_half,
    primeDepthBVWoldXiCenteredRate]
  constructor
  · intro h
    have hrate : 2 * (q.1 : ℂ).re - 1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hx
      nlinarith
    linarith
  · intro h
    rw [h]
    ring

/-- Curvature transgression capstone.  Every Xi divisor copy retains a nonzero terminal source
coefficient; its finite-cut holonomy simultaneously reconstructs the second-order descent defect
and detects its coherent-flat locus. -/
theorem xiTerminalMultiplicityJet_curvatureTransgression
    (q : XiZeroCopy) {cut : ℝ} (hcut : cut ≠ 0)
    (x : DeningerCalderonWittGlobalOrientedKoszulTotalCarrier) :
    xiThetaTerminalMultiplicityCutJet q.1 0 ≠ 0 ∧
      xiThetaTerminalMultiplicityCutLogGain q.1 cut =
        cut * primeDepthBVWoldXiCenteredRate q.1 / 2 ∧
      GaloisForLFunctions.HTGeometry.secondOrderConstraintDescentDefect
          deningerCalderonWittGlobalOrientedKoszulTotalDifferential
          deningerCalderonWittNodalTopObservation
          (xiNodalTotalDefectEnd q) x =
        (((2 * (q.1 : ℂ).im / cut *
            xiThetaTerminalMultiplicityCutLogGain q.1 cut : ℝ) : ℂ)) •
          deningerCalderonWittNodalTopObservation x ∧
      (xiThetaTerminalMultiplicityCutLogGain q.1 cut = 0 ↔
        XiNodalArithmeticSecondOrderCoherent q) := by
  exact ⟨xiThetaTerminalMultiplicityCutJet_ne_zero q.1 0,
    xiThetaTerminalMultiplicityCutLogGain_eq q.1 cut,
    xiNodalArithmeticSecondOrderDefect_apply_eq_terminalMultiplicityCutLogGain
      q hcut x,
    xiThetaTerminalMultiplicityCutLogGain_eq_zero_iff_nodalArithmeticSecondOrderCoherent
      q hcut⟩

end

end RHTower
