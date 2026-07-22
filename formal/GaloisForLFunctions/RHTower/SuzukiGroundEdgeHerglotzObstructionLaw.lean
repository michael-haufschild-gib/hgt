import GaloisForLFunctions.RHTower.SuzukiGroundEdgeApertureObstruction

/-!
# Suzuki ground-edge Herglotz obstruction

The central Herglotz residue threshold is incompatible with every positive-mass ground edge above
the half-curvature moment floor.  Robin compression transports the same obstruction to an exact
even eigenmode boundary law.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Positive ground-edge no-go.**  A ground average forced strictly above Xi curvature cannot
simultaneously be the central source flux of a Herglotz affine-sewn exterior. -/
theorem not_suzukiAffineSewnExteriorWeylQuotient_herglotz_of_groundEdgeMoment
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    {alpha beta : ℂ} (hab : alpha ≠ beta)
    {moment mass : ℝ} (hmass : 0 < mass)
    (hmoment : (deriv (deriv XiC) 0 / XiC 0).re / 2 * mass ≤ moment)
    (hfluxAverage :
      (suzukiAffineSewnCentralSourceFlux alpha beta a b
        (rightAlpha 0) (rightBeta 0)).re =
          suzukiGroundEdgeAverage moment mass) :
    ¬ ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta z).im := by
  intro hHerglotz
  have hfluxLe :=
    suzukiAffineSewnCentralSourceFlux_re_le_XiC_curvature_of_herglotz
      hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hRightAlpha hRightBeta hab hHerglotz
  have havgGt :=
    suzukiGroundEdgeAverage_gt_XiC_curvature_of_half_lowerMoment hmass hmoment
  rw [hfluxAverage] at hfluxLe
  exact (not_lt_of_ge hfluxLe) havgGt

/-- **Robin-compressed ground-edge no-go.**  The exact even eigen-equation transports the same
obstruction to the boundary ratio `-lambda * U(a) / (2 * U'(a))`. -/
theorem not_suzukiAffineSewnExteriorWeylQuotient_herglotz_of_groundEdgeRobin
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    {alpha beta : ℂ} (hab : alpha ≠ beta)
    {eigenvalue boundaryValue boundarySlope mass : ℝ}
    (heigenvalue : eigenvalue ≠ 0) (hmass : 0 < mass)
    (hboundaryFlux : -2 * boundarySlope = eigenvalue * mass)
    (hboundaryMoment :
      (deriv (deriv XiC) 0 / XiC 0).re / 2 * mass ≤ boundaryValue)
    (hsourceFluxRobin :
      (suzukiAffineSewnCentralSourceFlux alpha beta a b
        (rightAlpha 0) (rightBeta 0)).re =
          suzukiGroundEdgeBoundaryRatio eigenvalue boundaryValue boundarySlope) :
    ¬ ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta z).im := by
  apply not_suzukiAffineSewnExteriorWeylQuotient_herglotz_of_groundEdgeMoment
    hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hRightAlpha hRightBeta hab
    hmass hboundaryMoment
  rw [hsourceFluxRobin,
    suzukiGroundEdgeBoundaryRatio_eq_average_of_flux
      heigenvalue hmass.ne' hboundaryFlux]

end

end RHTower
