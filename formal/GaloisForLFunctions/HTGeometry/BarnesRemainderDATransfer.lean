import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.AffineFirstOrderDifferentialAlgebraicity

/-!
# Differential-algebraic transfer to the Barnes remainder

If a canonical product is differentially algebraic, so is its Euler logarithmic derivative, and so
is the remainder left after subtracting the explicit terms of the Barnes expansion: a power
`x^{1/s}`, a polynomial in `x`, and a constant.

Each step is a closure property of differential algebraicity, all of which the differential-circuit
layer supplies: derivative, quotient, sum, difference.  The power term is differentially algebraic
because it satisfies the first-order affine equation `y′ = (1/(s x)) y`, whose coefficient lies in
the rational base field.

This is the algebraic half of the transfer; what it leaves open is the analytic half, the passage
from the asymptotic expansion of the remainder to a formal-series identity.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]

/-- **The Euler logarithmic derivative of a differentially algebraic element is differentially
algebraic.** -/
theorem differentialAlgebraicOver_eulerLogDeriv {x W : E}
    (hx : DifferentialAlgebraicOver F x) (hW : DifferentialAlgebraicOver F W) :
    DifferentialAlgebraicOver F (x * (W′ / W)) :=
  differentialAlgebraicOver_mul hx
    (differentialAlgebraicOver_div (differentialAlgebraicOver_deriv hW) hW)

omit [Differential F] [DifferentialAlgebra F E] [CharZero E] in
/-- **The Euler eigenfunction is differentially algebraic.**  An element satisfying `y′ = c y` with
`c` in the base field — the equation `x y′ = (1/s) y` after dividing by `x` — is differentially
algebraic over that base. -/
theorem differentialAlgebraicOver_eulerEigen {y : E} (c : F)
    (hrel : y′ = algebraMap F E c * y) :
    DifferentialAlgebraicOver F y := by
  refine differentialAlgebraicOver_of_deriv_eq_base_mul_add c 0 ?_
  simpa using hrel

/-- **The Barnes remainder inherits differential algebraicity.**  Subtracting the explicit terms of
the expansion — the power, the polynomial part and the constant — from the Euler logarithmic
derivative leaves a differentially algebraic remainder. -/
theorem differentialAlgebraicOver_barnesRemainder {x W u P R : E}
    (hx : DifferentialAlgebraicOver F x) (hW : DifferentialAlgebraicOver F W)
    (hu : DifferentialAlgebraicOver F u) (hP : DifferentialAlgebraicOver F P)
    (hR : R = x * (W′ / W) - (u + P)) :
    DifferentialAlgebraicOver F R := by
  rw [hR]
  exact differentialAlgebraicOver_sub (differentialAlgebraicOver_eulerLogDeriv hx hW)
    (differentialAlgebraicOver_add hu hP)

/-- The same conclusion with the power term presented by its defining equation. -/
theorem differentialAlgebraicOver_barnesRemainder_of_eulerEigen {x W u P R : E} (c : F)
    (hx : DifferentialAlgebraicOver F x) (hW : DifferentialAlgebraicOver F W)
    (hu : u′ = algebraMap F E c * u) (hP : DifferentialAlgebraicOver F P)
    (hR : R = x * (W′ / W) - (u + P)) :
    DifferentialAlgebraicOver F R :=
  differentialAlgebraicOver_barnesRemainder hx hW (differentialAlgebraicOver_eulerEigen c hu) hP hR

end

end GaloisForLFunctions.HTGeometry
