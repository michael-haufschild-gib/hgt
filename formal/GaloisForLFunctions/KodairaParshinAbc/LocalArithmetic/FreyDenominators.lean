import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.SplitCurveDenominators
import Mathlib.Data.Fin.VecNotation

/-!
# Square denominators on the integral Frey equation

The three integral roots of `x(x-a)(x+b)` make the general odd-degree
denominator theorem apply to every rational solution of the Frey equation.
Primitivity, nonsingularity, and restrictions on the prime are unnecessary.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open HTGeometry.Arithmetic

/-- Rational x-coordinates on any integral Frey equation have square
reduced denominator, including singular specializations. -/
theorem frey_equation_squareDenominator (a b : ℤ) {x y : ℚ}
    (hcurve : y ^ 2 = x * (x - (a : ℚ)) * (x + (b : ℚ))) :
    SquareDenominator x := by
  apply squareDenominator_of_odd_split_curve
    (Finset.univ : Finset (Fin 3)) ![0, a, -b]
    (by exact ⟨1, by simp⟩)
  simpa [Fin.prod_univ_three] using hcurve

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
