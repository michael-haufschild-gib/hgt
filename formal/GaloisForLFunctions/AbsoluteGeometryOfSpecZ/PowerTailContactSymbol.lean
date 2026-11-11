import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailContactDirichletCoefficients
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel

/-!
# The shifted zeta symbol of power-tail contacts

The polar subtraction isolates a coefficient sequence whose Dirichlet
symbol has the rightmost zeta poles shifted by the power exponent.
-/

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Contact coefficients after subtracting the leading polar contribution. -/
def powerTailDefectCoefficient (a : ℝ) (n : ℕ) : ℂ :=
  (powerTailContactCoefficient a n : ℂ) -
    riemannZeta (1 + (a : ℂ)) * (powerTailWeight a n : ℂ)

/-- The meromorphic symbol predicted by the exact divisor coefficients. -/
def powerTailContactSymbol (a : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + 2 * (a : ℂ)) * (-(deriv riemannZeta (s + (a : ℂ))) /
    riemannZeta (s + (a : ℂ))) -
      riemannZeta (1 + (a : ℂ)) * riemannZeta (s + (a : ℂ))

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
