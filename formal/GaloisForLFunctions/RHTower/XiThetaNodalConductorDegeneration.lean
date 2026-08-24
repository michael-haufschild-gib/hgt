import GaloisForLFunctions.RHTower.FrankensteinGammaCompositionScaleZeroDescent

/-!
# Source-first Xi nodal conductor degeneration

The completed theta function pulls the universal affine node `x*y=t` back to
`x*y=XiC(z)` before any zero is selected.  At every Xi divisor point its reduced set-theoretic
fibre is exactly the union of the two coordinate axes.  The companion projective Legendre equation
specializes to one fixed nodal cubic.

This is both a construction and a no-go: all reduced fibres are identical, so reduced nodal
geometry cannot see horizontal location or analytic multiplicity.  The latter must travel in the
scheme-theoretic Cartier/conormal channel.  This file deliberately does not claim that the affine
model is a proper analytic family or construct the missing conductor-to-nearby-cycle regulator.
-/

namespace RHTower

noncomputable section

/-- Source-first affine node equation pulled back along the completed theta function. -/
def xiThetaNodeEquation (z x y : ℂ) : ℂ :=
  x * y - XiC z

/-- Set-theoretic affine fibre of the pulled-back universal node at an Xi divisor point. -/
def xiThetaNodeFiber (rho : XiDivisorSupport) : Set (ℂ × ℂ) :=
  {p | xiThetaNodeEquation (xiSpectralPointSupport rho) p.1 p.2 = 0}

@[simp]
theorem xiThetaNodeEquation_at_divisor
    (rho : XiDivisorSupport) (x y : ℂ) :
    xiThetaNodeEquation (xiSpectralPointSupport rho) x y = x * y := by
  simp [xiThetaNodeEquation, XiC_xiSpectralPointSupport_eq_zero]

/-- Every Xi fibre of the raw node is exactly the union of its two coordinate branches. -/
theorem mem_xiThetaNodeFiber_iff
    (rho : XiDivisorSupport) (p : ℂ × ℂ) :
    p ∈ xiThetaNodeFiber rho ↔ p.1 = 0 ∨ p.2 = 0 := by
  simp [xiThetaNodeFiber, xiThetaNodeEquation_at_divisor]

/-- Reduced fibre as a set: union of the two transverse coordinate axes. -/
theorem xiThetaNodeFiber_eq_coordinateAxes (rho : XiDivisorSupport) :
    xiThetaNodeFiber rho =
      ({p : ℂ × ℂ | p.1 = 0} ∪ {p : ℂ × ℂ | p.2 = 0}) := by
  ext p
  simp [mem_xiThetaNodeFiber_iff]

/-- The reduced node is support-blind; all Xi location and multiplicity data lies elsewhere. -/
theorem xiThetaNodeFiber_eq_xiThetaNodeFiber
    (rho sigma : XiDivisorSupport) :
    xiThetaNodeFiber rho = xiThetaNodeFiber sigma := by
  rw [xiThetaNodeFiber_eq_coordinateAxes, xiThetaNodeFiber_eq_coordinateAxes]

/-- Projective Legendre equation pulled back along the completed theta function. -/
def xiThetaLegendreEquation (z X Y Z : ℂ) : ℂ :=
  Y ^ 2 * Z - X * (X - Z) * (X - XiC z * Z)

/-- Every Xi divisor fibre of the global Legendre equation is the same nodal cubic equation. -/
@[simp]
theorem xiThetaLegendreEquation_at_divisor
    (rho : XiDivisorSupport) (X Y Z : ℂ) :
    xiThetaLegendreEquation (xiSpectralPointSupport rho) X Y Z =
      Y ^ 2 * Z - X ^ 2 * (X - Z) := by
  rw [xiThetaLegendreEquation, XiC_xiSpectralPointSupport_eq_zero]
  ring

end

end RHTower
