import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioNonlinearBoundaryParameter
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicNormalForm
/-!
# Complete source slope on the exact nonlinear boundary

The polynomial parametrization differs from the cubic comparison sheet by
an exact fourth-order term. The full cubic normal form therefore gives
`scaledSlope=h^3*nonlinearBoundaryCore` at every parameter value and
`h^16*sourceSlope=nonlinearBoundaryCore` for nonzero clock.
All normal derivatives belong to the original source slope. The sign of
this complete boundary core on the physical domain remains open.
-/
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def nonlinearBoundaryCubicGap (h s : ℂ) : ℂ :=
  nonlinearBoundarySeed h*s^3*(2-h^2*nonlinearBoundarySeed h*s)*(1/144-7*h/432)+
    49*s^2/5184

theorem nonlinearBoundary_cubic_gap (h s : ℂ) :
    nonlinearBoundaryT h s-
      (nonlinearBoundaryR h s*nonlinearBoundarySeed h+
        (nonlinearBoundaryR h s)^2*h^2/144-7*(nonlinearBoundaryR h s)^2*h^3/432)=
      h^4*nonlinearBoundaryCubicGap h s := by
  unfold nonlinearBoundaryT nonlinearBoundaryR nonlinearBoundaryCubicGap nonlinearBoundarySeed
  ring

def nonlinearBoundaryCore (h s : ℂ) : ℂ :=
  eval (basePoint h (nonlinearBoundaryR h s) 0) nonlinearCubicCore+
    h*nonlinearBoundaryCubicGap h s*
      eval (basePoint h (nonlinearBoundaryR h s) (h^4*nonlinearBoundaryCubicGap h s))
        nonlinearTransverseCore

theorem nonlinearBoundary_scaledSlope (h s : ℂ) :
    eval (basePoint h (nonlinearBoundaryR h s) (nonlinearBoundaryT h s)) scaledSlope=
      h^3*nonlinearBoundaryCore h s := by
  have hg := nonlinearBoundary_cubic_gap h s
  dsimp only [nonlinearBoundarySeed] at hg
  have ht : h^4*nonlinearBoundaryCubicGap h s+
      nonlinearBoundaryR h s*(1/12-7*h/72)+
      ((nonlinearBoundaryR h s)^2/144)*h^2-
      (7*(nonlinearBoundaryR h s)^2/432)*h^3=nonlinearBoundaryT h s := by
    linear_combination -hg
  have hn := nonlinearSlope_normal_form h (nonlinearBoundaryR h s)
    (h^4*nonlinearBoundaryCubicGap h s)
  rw [nonlinearShift_eval,ht] at hn
  rw [hn]
  unfold nonlinearBoundaryCore
  ring

theorem nonlinearBoundary_sourcePoint (h s : ℂ) :
    sourcePoint h (nonlinearBoundaryR h s) (nonlinearBoundaryT h s)=
      basePoint (nonlinearBoundaryV h s) h⁻¹ (nonlinearBoundaryZ h s) := by
  funext i
  cases i <;> simp [sourcePoint,basePoint,nonlinearBoundaryV,nonlinearBoundaryZ]
  all_goals ring

theorem nonlinearBoundary_sourceSlope {h : ℂ} (hh : h≠0) (s : ℂ) :
    h^16*eval (basePoint (nonlinearBoundaryV h s) h⁻¹ (nonlinearBoundaryZ h s)) ThetaRatioSquare.slope=
      nonlinearBoundaryCore h s := by
  apply mul_left_cancel₀ (pow_ne_zero 3 hh)
  calc
    _ = h^19*eval (basePoint (nonlinearBoundaryV h s) h⁻¹ (nonlinearBoundaryZ h s)) ThetaRatioSquare.slope := by ring
    _ = eval (basePoint h (nonlinearBoundaryR h s) (nonlinearBoundaryT h s)) scaledSlope := by
      simpa only [nonlinearBoundary_sourcePoint] using
        scaledSlope_eq h (nonlinearBoundaryR h s) (nonlinearBoundaryT h s) hh
    _ = _ := nonlinearBoundary_scaledSlope h s

theorem nonlinearBoundaryCore_zero (s : ℂ) :
    nonlinearBoundaryCore 0 s=1944*axisMinorMass-63*principalMass*s^2 := by
  simpa [nonlinearBoundaryCore,nonlinearBoundaryR] using nonlinearCubicCore_zero s

end
end HTGeometry.ThetaRatioInfinity
