import GaloisForLFunctions.Bottcher.WindingBasepoint
import Mathlib.Analysis.Complex.Circle

/-!
# Pointed abelian Wilson loops

`Bottcher.windPt` already assigns an integer winding charge to a loop avoiding a marked point.  This
file packages that data as a Wilson loop and proves its unit-level abelian Chern--Simons holonomy is
trivial.  It is a loop invariant in a punctured plane, not a three-dimensional knot invariant.
-/

open unitInterval

namespace Bottcher

noncomputable section

/-- A based loop together with a puncture which it avoids. -/
structure PointedWilsonLoop where
  base : ℂ
  loop : Path base base
  puncture : ℂ
  avoids : ∀ t : I, (loop t : ℂ) ≠ puncture

/-- Integer Wilson charge: winding of the loop around its designated puncture. -/
def PointedWilsonLoop.windingCharge (L : PointedWilsonLoop) : ℤ :=
  windPt L.loop L.puncture L.avoids

/-- Unit-level abelian Chern--Simons Wilson holonomy. -/
def PointedWilsonLoop.unitWilsonHolonomy (L : PointedWilsonLoop) : ℂ :=
  Complex.exp ((L.windingCharge : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))

/-- Integer winding gives trivial holonomy at integral level one. -/
theorem PointedWilsonLoop.unitWilsonHolonomy_eq_one (L : PointedWilsonLoop) :
    L.unitWilsonHolonomy = 1 :=
  Complex.exp_int_mul_two_pi_mul_I L.windingCharge

end

end Bottcher
