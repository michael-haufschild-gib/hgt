import GaloisForLFunctions.HTGeometry.EulerPolePartCalculus

/-!
# The principal-part monomials `(x − α)^{-d}`

These are the building blocks of a partial-fraction decomposition.  Their principal-part
coefficients are the Kronecker delta at `(α, d)`, and they are regular away from `α`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- The principal-part monomial `(x − α)^{-d}`. -/
def invLinPow (α : K) (d : ℕ) : RatFunc K :=
  (algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ d))⁻¹

theorem ratFuncShift_invLinPow (α : K) (d : ℕ) :
    ratFuncShift α (invLinPow α d)
      = (algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X : Polynomial K) ^ d))⁻¹ := by
  rw [invLinPow, map_inv₀, ratFuncShift_algebraMap]
  congr 2
  rw [map_pow]
  congr 1
  rw [map_sub, polyShift_apply, polyShift_apply, Polynomial.X_comp, Polynomial.C_comp]
  ring

theorem algebraMap_X_pow_laurent (d : ℕ) :
    algebraMap (RatFunc K) (LaurentSeries K)
        (algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X : Polynomial K) ^ d))
      = HahnSeries.single (d : ℤ) 1 := by
  rw [map_pow, RatFunc.algebraMap_X, map_pow, RatFunc.coe_X, ← RatFunc.single_one_eq_pow]

theorem algebraMap_ratFuncShift_invLinPow (α : K) (d : ℕ) :
    algebraMap (RatFunc K) (LaurentSeries K) (ratFuncShift α (invLinPow α d))
      = HahnSeries.single (-(d : ℤ)) 1 := by
  rw [ratFuncShift_invLinPow, map_inv₀, algebraMap_X_pow_laurent, HahnSeries.inv_single, inv_one]

theorem polePart_invLinPow_self (α : K) (d e : ℕ) :
    polePart (invLinPow α d) α e = if e = d then 1 else 0 := by
  rw [polePart, algebraMap_ratFuncShift_invLinPow]
  by_cases h : e = d
  · subst h
    simp
  · rw [if_neg h, HahnSeries.coeff_single_of_ne]
    omega

theorem regularAt_invLinPow {α β : K} (h : β ≠ α) (d : ℕ) : RegularAt (invLinPow α d) β := by
  refine regularAt_of_repr (P := 1) (Q := (Polynomial.X - Polynomial.C α) ^ d) ?_ ?_
  · rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact pow_ne_zero _ (sub_ne_zero.2 h)
  · rw [invLinPow, map_one, one_div]

theorem polePart_invLinPow_of_ne {α β : K} (h : β ≠ α) (d e : ℕ) (he : 0 < e) :
    polePart (invLinPow α d) β e = 0 :=
  polePart_eq_zero_of_poleOrder_zero he
    ((regularAt_iff_poleOrder_eq_zero _ _).1 (regularAt_invLinPow h d))

end

end GaloisForLFunctions.HTGeometry
