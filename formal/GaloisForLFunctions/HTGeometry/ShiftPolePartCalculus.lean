import GaloisForLFunctions.HTGeometry.EulerPolePartCalculus
import GaloisForLFunctions.HTGeometry.EulerOrdinaryDerivationBridge

/-!
# Pole parts under the ordinary derivative and under translation

Differentiating a rational function shifts its principal part one order up with the factor `-d`,
and translating it moves the pole location.  These are the two transformation laws behind the
orbit obstruction for a first-order inhomogeneous shift equation.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- **The ordinary derivative on principal parts.** -/
theorem polePart_ratFuncDerivative (f : RatFunc K) (c : K) (d : ℕ) :
    polePart (ratFuncDerivative K f) c (d + 1) = -(d : K) * polePart f c d := by
  rw [polePart, ← ratFuncShift_ratFuncDerivative, algebraMap_ratFuncDerivative]
  set G : LaurentSeries K := algebraMap (RatFunc K) (LaurentSeries K) (ratFuncShift c f) with hG
  rw [HahnSeries.coeff_single_mul, coeff_innerEuler]
  have hidx : (-((d + 1 : ℕ) : ℤ) - (-1 : ℤ)) = -((d : ℕ) : ℤ) := by push_cast; ring
  rw [hidx, polePart, ← hG]
  push_cast
  ring

/-- **Translation moves the pole location.** -/
theorem polePart_ratFuncShift (f : RatFunc K) (a c : K) (d : ℕ) :
    polePart (ratFuncShift a f) c d = polePart f (c + a) d := by
  rw [polePart, polePart]
  congr 2
  show ratFuncShift c (ratFuncShift a f) = ratFuncShift (c + a) f
  refine RatFunc.induction_on (P := fun f =>
    ratFuncShift c (ratFuncShift a f) = ratFuncShift (c + a) f) f ?_
  intro P S _
  rw [ratFuncShift_div, ratFuncShift_div, ratFuncShift_div]
  congr 1 <;>
    · congr 1
      simp only [polyTranslate_apply, Polynomial.comp_assoc]
      congr 1
      rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_add]
      ring

end

end GaloisForLFunctions.HTGeometry
