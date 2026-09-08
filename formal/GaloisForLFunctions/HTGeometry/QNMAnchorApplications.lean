import GaloisForLFunctions.HTGeometry.Arxiv2026Applications

/-!
# QNMAnchorApplications

Applying the Kerr PINN affine anchor to existing Faraday, Bessel, and vortex
residuals exposes exact constant-mode defects. The fourth-order Faraday
application starts from the corpus actual exponential modes.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem faradayRadialBesselResidual_qnmAnchor
    (m : ℤ) (beta r value first second anchorValue : ℝ) :
    faradayRadialBesselResidual m beta r (1 + value - anchorValue) first second =
      faradayRadialBesselResidual m beta r value first second +
        (beta ^ 2 - (m : ℝ) ^ 2 / r ^ 2) * (1 - anchorValue) := by
  unfold faradayRadialBesselResidual
  ring

theorem vortexLinearStationaryResidual_qnmAnchor
    (ell : ℤ) (waveSq r value second anchorValue : ℝ) :
    vortexLinearStationaryResidual ell waveSq r (1 + value - anchorValue) second =
      vortexLinearStationaryResidual ell waveSq r value second +
        (waveSq - vortexCentrifugalCoefficient ell / r ^ 2) * (1 - anchorValue) := by
  unfold vortexLinearStationaryResidual
  ring

theorem faradayVerticalMode_qnmAnchor_residual
    (beta q a b c d z anchor : ℝ) :
    faradayVerticalModeJet beta q a b c d 4 z -
        (beta ^ 2 + q ^ 2) * faradayVerticalModeJet beta q a b c d 2 z +
        beta ^ 2 * q ^ 2 * (1 + faradayVerticalModeJet beta q a b c d 0 z -
          faradayVerticalModeJet beta q a b c d 0 anchor) =
      beta ^ 2 * q ^ 2 * (1 - faradayVerticalModeJet beta q a b c d 0 anchor) := by
  have h := faradayVerticalMode_factored_ode beta q a b c d z
  linear_combination h

end GaloisForLFunctions.HTGeometry
