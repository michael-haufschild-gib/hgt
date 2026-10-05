import GaloisForLFunctions.RHTower.ThetaCuspRatioNonlinearBoundaryPolynomial
/-!
The polynomial quotient by the drift factor agrees with h^16 times
the complete reduced source slope, including V=0. Denominator clearing
and polynomial cancellation avoid any nonzero-drift hypothesis.
Global positivity on the physical parameter domain remains open.
-/
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

theorem reducedNonlinearBoundaryCore_source {h : ℂ} (hh : h≠0) (s u : ℂ) :
    eval (basePoint h s u) reducedNonlinearBoundaryCore=
      h^16*eval (basePoint (nonlinearBoundaryV h s) h⁻¹ (nonlinearBoundaryZ h s))
        reducedSlope := by
  obtain ⟨n,Q,hQ⟩ := sourcePolynomial_regularization reducedSlope
  let Qp := nonlinearBoundaryLift nonlinearBoundaryTPoly Q
  have hQp (h s u : ℂ) (hh : h≠0) :
      eval (basePoint h s u) Qp=
        h^n*eval (sourcePoint h (nonlinearBoundaryR h s) (nonlinearBoundaryT h s))
          reducedSlope := by
    dsimp only [Qp]
    rw [nonlinearBoundaryLift_eval,nonlinearBoundaryTPoly_eval]
    exact (hQ _ _ _ hh).symm
  have hp : nonlinearBoundaryVPoly*((X Coord.U)^n*reducedNonlinearBoundaryCore)=
      nonlinearBoundaryVPoly*((X Coord.U)^16*Qp) := by
    apply polynomial_ext_clock_nonzero
    intro h s u hh
    have hs := nonlinearBoundary_sourceSlope hh s
    rw [←nonlinearBoundary_sourcePoint] at hs
    have hf : nonlinearBoundaryVPoly*((X Coord.U)^n*reducedNonlinearBoundaryCore)=
        (X Coord.U)^n*nonlinearBoundaryCorePoly := by
      rw [nonlinearBoundaryCorePoly_factor]
      ring
    rw [hf]
    simp only [map_mul,map_pow,eval_X,basePoint,nonlinearBoundaryCorePoly_eval,
      nonlinearBoundaryVPoly_eval]
    rw [←hs,slope_seam_factor,hQp h s u hh]
    simp only [map_mul,eval_X,sourcePoint]
    dsimp only [nonlinearBoundaryV]
    ring
  have hc := mul_left_cancel₀ nonlinearBoundaryVPoly_ne_zero hp
  have hv := congrArg (eval (basePoint h s u)) hc
  simp only [map_mul,map_pow,eval_X,basePoint] at hv
  apply mul_left_cancel₀ (pow_ne_zero n hh)
  calc
    _ = h^16*eval (basePoint h s u) Qp := hv
    _ = _ := by rw [hQp h s u hh,nonlinearBoundary_sourcePoint]; ring

theorem reducedNonlinearBoundaryCore_zero (s u : ℂ) :
    eval (basePoint 0 s u) reducedNonlinearBoundaryCore=
      216*axisMinorMass-7*principalMass*s^2 := by
  have he := congrArg (eval (basePoint 0 s u)) nonlinearBoundaryCorePoly_factor
  simp only [nonlinearBoundaryCorePoly_eval,map_mul,nonlinearBoundaryVPoly_eval] at he
  rw [nonlinearBoundaryCore_zero] at he
  norm_num [nonlinearBoundaryV,nonlinearBoundaryR] at he
  linear_combination -he/9

end
end HTGeometry.ThetaRatioInfinity
