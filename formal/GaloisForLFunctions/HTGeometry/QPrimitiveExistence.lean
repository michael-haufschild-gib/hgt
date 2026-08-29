import GaloisForLFunctions.HTGeometry.QOrbitResidueTop

/-!
# The `q`-primitive of a rational increment

A Laurent series supported in positive degrees solves `f(qx) − f(x) = r(x)` coefficientwise, with
`f`'s coefficients `r_n/(q^n − 1)`; the only obstruction is the constant term of `r`, which the
regularity and vanishing of `r` at the origin removes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- The coefficientwise `q`-primitive of a Laurent series. -/
def qPrimitive (q : K) (r : LaurentSeries K) : LaurentSeries K where
  coeff n := r.coeff n / (q ^ n - 1)
  isPWO_support' := by
    refine Set.IsPWO.mono r.isPWO_support ?_
    intro n hn
    simp only [Function.mem_support] at hn
    rw [HahnSeries.mem_support]
    intro h0
    exact hn (by rw [h0, zero_div])

@[simp] theorem coeff_qPrimitive (q : K) (r : LaurentSeries K) (n : ℤ) :
    (qPrimitive q r).coeff n = r.coeff n / (q ^ n - 1) := rfl

/-- **The `q`-primitive solves the difference equation.** -/
theorem innerDilation_qPrimitive {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (r : LaurentSeries K) (hr0 : r.coeff 0 = 0) :
    innerDilation q hq (qPrimitive q r) = qPrimitive q r + r := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_innerDilation, HahnSeries.coeff_add]
  simp only [coeff_qPrimitive]
  by_cases hn : n = 0
  · subst hn
    rw [hr0]
    simp
  · have hqn : q ^ n - 1 ≠ 0 := sub_ne_zero.2 (hqtor n hn)
    field_simp
    ring

theorem ratFuncShift_zero (r : RatFunc K) : ratFuncShift 0 r = r := by
  refine RatFunc.induction_on (P := fun r => ratFuncShift 0 r = r) r ?_
  intro P S _
  rw [ratFuncShift_div, polyShift_apply, polyShift_apply, map_zero, add_zero,
    Polynomial.comp_X, Polynomial.comp_X]

theorem coeff_algebraMap_ratFunc (r : RatFunc K) (d : ℕ) :
    (algebraMap (RatFunc K) (LaurentSeries K) r).coeff (-(d : ℤ)) = polePart r 0 d := by
  rw [polePart, ratFuncShift_zero]

end

end GaloisForLFunctions.HTGeometry
