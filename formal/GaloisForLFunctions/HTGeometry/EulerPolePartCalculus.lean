import GaloisForLFunctions.HTGeometry.RationalPolePart
import GaloisForLFunctions.HTGeometry.EulerOrdinaryDerivationBridge

/-!
# The Euler operator on principal parts

Translation commutes with differentiation, so the Euler operator `z d/dz` acts on the expansion of
a rational function at a point `c` as `(t + c) d/dt`.  Reading off the coefficient of `t^(−d−1)`
gives the transformation law of the principal parts: the top-order coefficient is multiplied by
`−c·d` at each step, which is what makes the jets of a pole increment nondegenerate.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

theorem polyTranslate_derivative (c : K) (P : Polynomial K) :
    Polynomial.derivative (polyTranslate c P) = polyTranslate c (Polynomial.derivative P) := by
  rw [polyTranslate_apply, polyTranslate_apply, Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, one_mul]

theorem ratFuncShift_algebraMap (c : K) (R : Polynomial K) :
    ratFuncShift c (algebraMap (Polynomial K) (RatFunc K) R)
      = algebraMap (Polynomial K) (RatFunc K) (polyTranslate c R) := by
  have h := ratFuncShift_div c R 1
  simpa using h

theorem ratFuncShift_ratFuncDerivative (c : K) (f : RatFunc K) :
    ratFuncDerivative K (ratFuncShift c f) = ratFuncShift c (ratFuncDerivative K f) := by
  refine RatFunc.induction_on (P := fun f =>
    ratFuncDerivative K (ratFuncShift c f) = ratFuncShift c (ratFuncDerivative K f)) f ?_
  intro P S _
  rw [ratFuncShift_div, Derivation.leibniz_div, Derivation.leibniz_div]
  simp only [smul_eq_mul, map_mul, map_sub, map_inv₀, map_pow, ratFuncShift_algebraMap,
    ratFuncDerivative_algebraMap, polyTranslate_derivative]

theorem ratFuncShift_X (c : K) :
    ratFuncShift c (RatFunc.X : RatFunc K) = RatFunc.X + algebraMap K (RatFunc K) c := by
  have hX : (RatFunc.X : RatFunc K)
      = algebraMap (Polynomial K) (RatFunc K) Polynomial.X := (RatFunc.algebraMap_X).symm
  rw [hX, ratFuncShift_algebraMap, polyTranslate_apply, Polynomial.X_comp, map_add,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The Euler operator on principal parts.** -/
theorem polePart_eulerOp (f : RatFunc K) (c : K) (d : ℕ) :
    polePart (ratFuncEulerOp f) c (d + 1)
      = (((-(d : ℤ) - 1 : ℤ) : K)) * polePart f c (d + 1)
        + c * (((-(d : ℤ) : ℤ) : K)) * polePart f c d := by
  have hshift : ratFuncShift c (ratFuncEulerOp f)
      = (RatFunc.X + algebraMap K (RatFunc K) c) * ratFuncDerivative K (ratFuncShift c f) := by
    rw [ratFuncEulerOp_eq_X_mul, map_mul, ratFuncShift_X, ratFuncShift_ratFuncDerivative]
  have hconst : algebraMap (RatFunc K) (LaurentSeries K)
      (RatFunc.X + algebraMap K (RatFunc K) c)
      = HahnSeries.single 1 1 + HahnSeries.single 0 c := by
    rw [map_add, algebraMap_ratFuncX, laurentCoord, algebraMap_const_laurentSeries]
  rw [polePart, hshift, map_mul, hconst, algebraMap_ratFuncDerivative]
  set G : LaurentSeries K := algebraMap (RatFunc K) (LaurentSeries K) (ratFuncShift c f) with hG
  have hprod : (HahnSeries.single (1 : ℤ) (1 : K) + HahnSeries.single 0 c)
      * (HahnSeries.single (-1 : ℤ) 1 * innerEuler G)
      = innerEuler G + HahnSeries.single (-1 : ℤ) c * innerEuler G := by
    rw [add_mul, ← mul_assoc, ← mul_assoc, HahnSeries.single_mul_single,
      HahnSeries.single_mul_single]
    norm_num
  rw [hprod, HahnSeries.coeff_add, HahnSeries.coeff_single_mul, coeff_innerEuler,
    coeff_innerEuler,
    show (-(((d + 1 : ℕ)) : ℤ) - (-1 : ℤ)) = -((d : ℕ) : ℤ) from by push_cast; ring,
    polePart, polePart, ← hG]
  push_cast
  ring

/-! ## Reading the top-order coefficient -/

theorem algebraMap_mul_single (F : RatFunc K) (m : ℕ) :
    algebraMap (RatFunc K) (LaurentSeries K) (F * RatFunc.X ^ m)
      = algebraMap (RatFunc K) (LaurentSeries K) F * HahnSeries.single (m : ℤ) 1 := by
  rw [map_mul, map_pow, algebraMap_ratFuncX, laurentCoord, HahnSeries.single_pow, one_pow]
  congr 1
  simp

theorem coeff_of_regular_mul_X_pow {F : RatFunc K} {m : ℕ}
    (h : RegularAt (F * RatFunc.X ^ m) 0) {n : ℤ} (hn : n + (m : ℤ) < 0) :
    (algebraMap (RatFunc K) (LaurentSeries K) F).coeff n = 0 := by
  obtain ⟨P, Q, hQ, hrepr⟩ := h
  have hcoeff : (algebraMap (RatFunc K) (LaurentSeries K) (F * RatFunc.X ^ m)).coeff (n + m)
      = 0 := by
    rw [hrepr]
    exact coeff_neg_algebraMap_eq_zero_of_denom_ne_zero P Q hQ _ hn
  rw [algebraMap_mul_single, HahnSeries.coeff_mul_single] at hcoeff
  rw [show n + (m : ℤ) - (m : ℤ) = n from by ring] at hcoeff
  simpa using hcoeff

theorem coeff_zero_algebraMap_div (P Q : Polynomial K) (hQ : Q.eval 0 ≠ 0) :
    (algebraMap (RatFunc K) (LaurentSeries K)
      (algebraMap (Polynomial K) (RatFunc K) P
        / algebraMap (Polynomial K) (RatFunc K) Q)).coeff 0
      = P.eval 0 / Q.eval 0 := by
  have hconst : PowerSeries.constantCoeff (Q : PowerSeries K) ≠ 0 := by
    intro h
    apply hQ
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa using h
  have hinv : ((Q : PowerSeries K)) * ((Q : PowerSeries K))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hconst
  have hcoe : ∀ R : Polynomial K,
      algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) R)
        = ((R : PowerSeries K) : LaurentSeries K) := fun R => (RatFunc.coe_coe R).symm
  have hQne : ((Q : PowerSeries K) : LaurentSeries K) ≠ 0 := by
    intro h
    have := congrArg (fun x : LaurentSeries K => x.coeff 0) h
    rw [PowerSeries.coeff_coe, if_neg (by omega : ¬ (0 : ℤ) < 0), HahnSeries.coeff_zero] at this
    exact hconst (by simpa using this)
  have hdiv : algebraMap (RatFunc K) (LaurentSeries K)
      (algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q)
      = (((P : PowerSeries K) * ((Q : PowerSeries K))⁻¹ : PowerSeries K) : LaurentSeries K) := by
    rw [map_div₀, hcoe, hcoe, div_eq_iff hQne, ← map_mul]
    congr 1
    rw [mul_assoc, mul_comm ((Q : PowerSeries K))⁻¹, hinv, mul_one]
  rw [hdiv, PowerSeries.coeff_coe, if_neg (by omega : ¬ (0 : ℤ) < 0)]
  have hzero : ((0 : ℤ)).natAbs = 0 := rfl
  rw [hzero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    PowerSeries.constantCoeff_inv,
    show PowerSeries.constantCoeff (P : PowerSeries K) = P.eval 0 from by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      simp,
    show PowerSeries.constantCoeff (Q : PowerSeries K) = Q.eval 0 from by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      simp,
    div_eq_mul_inv]

/-! ## Jets of a pole -/

theorem polePart_eulerOp_vanish {g : RatFunc K} {c : K} {E : ℕ}
    (h : ∀ e : ℕ, E < e → polePart g c e = 0) :
    ∀ e : ℕ, E + 1 < e → polePart (ratFuncEulerOp g) c e = 0 := by
  intro e he
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  rw [polePart_eulerOp, h (d + 1) (by omega), h d (by omega), mul_zero, mul_zero, add_zero]

theorem polePart_eulerOp_top {g : RatFunc K} {c : K} {E : ℕ}
    (h : ∀ e : ℕ, E < e → polePart g c e = 0) :
    polePart (ratFuncEulerOp g) c (E + 1) = -(c * (E : K)) * polePart g c E := by
  rw [polePart_eulerOp, h (E + 1) (by omega), mul_zero, zero_add]
  push_cast
  ring

theorem polePart_eulerOp_regular {g : RatFunc K} {c : K}
    (h : ∀ e : ℕ, 0 < e → polePart g c e = 0) :
    ∀ e : ℕ, 0 < e → polePart (ratFuncEulerOp g) c e = 0 := by
  intro e he
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  rw [polePart_eulerOp, h (d + 1) (by omega), mul_zero, zero_add]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    norm_num
  · rw [h d hd, mul_zero]

theorem polePart_eulerOp_iterate_regular {g : RatFunc K} {c : K}
    (h : ∀ e : ℕ, 0 < e → polePart g c e = 0) (J : ℕ) :
    ∀ e : ℕ, 0 < e → polePart (ratFuncEulerOp^[J] g) c e = 0 := by
  induction J with
  | zero => simpa using h
  | succ J ih =>
      intro e he
      rw [Function.iterate_succ_apply']
      exact polePart_eulerOp_regular ih e he

theorem polePart_eulerOp_iterate {g : RatFunc K} {c : K} {m : ℕ}
    (h : ∀ e : ℕ, m < e → polePart g c e = 0) (J : ℕ) :
    (∀ e : ℕ, m + J < e → polePart (ratFuncEulerOp^[J] g) c e = 0)
      ∧ polePart (ratFuncEulerOp^[J] g) c (m + J)
        = (∏ i ∈ Finset.range J, -(c * ((m : K) + i))) * polePart g c m := by
  induction J with
  | zero => simpa using h
  | succ J ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨fun e he => ?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact polePart_eulerOp_vanish ih1 e (by omega)
      · rw [Function.iterate_succ_apply', show m + (J + 1) = (m + J) + 1 from by omega,
          polePart_eulerOp_top ih1, ih2, Finset.prod_range_succ]
        push_cast
        ring

/-! ## Pole parts from a regular product -/

theorem ratFuncShift_const (c a : K) :
    ratFuncShift c (algebraMap K (RatFunc K) a) = algebraMap K (RatFunc K) a := by
  have hC : algebraMap K (RatFunc K) a
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) := (RatFunc.algebraMap_C a).symm
  rw [hC, ratFuncShift_algebraMap, polyTranslate_apply, Polynomial.C_comp]

theorem ratFuncShift_linear (c : K) :
    ratFuncShift c (RatFunc.X - algebraMap K (RatFunc K) c) = (RatFunc.X : RatFunc K) := by
  rw [map_sub, ratFuncShift_X, ratFuncShift_const]
  ring

theorem shift_mul_X_pow (c : K) (g : RatFunc K) (m : ℕ) :
    ratFuncShift c g * RatFunc.X ^ m
      = ratFuncShift c (g * (RatFunc.X - algebraMap K (RatFunc K) c) ^ m) := by
  rw [map_mul, map_pow, ratFuncShift_linear]

theorem polePart_eq_zero_of_regularAt_mul_pow {g : RatFunc K} {c : K} {m : ℕ}
    (h : RegularAt (g * (RatFunc.X - algebraMap K (RatFunc K) c) ^ m) c) {e : ℕ} (he : m < e) :
    polePart g c e = 0 := by
  refine coeff_of_regular_mul_X_pow (m := m) ?_ (by omega)
  rw [shift_mul_X_pow]
  exact regularAt_ratFuncShift h

theorem polePart_top_of_repr {g : RatFunc K} {c : K} {m : ℕ} {P Q : Polynomial K}
    (hQ : Q.eval c ≠ 0)
    (h : g * (RatFunc.X - algebraMap K (RatFunc K) c) ^ m
      = algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q) :
    polePart g c m = P.eval c / Q.eval c := by
  have hshift : ratFuncShift c g * RatFunc.X ^ m
      = algebraMap (Polynomial K) (RatFunc K) (polyTranslate c P)
        / algebraMap (Polynomial K) (RatFunc K) (polyTranslate c Q) := by
    rw [shift_mul_X_pow, h, ratFuncShift_div]
  have hQ0 : (polyTranslate c Q).eval 0 ≠ 0 := by
    rw [polyTranslate_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, zero_add]
    exact hQ
  have hcoeff := coeff_zero_algebraMap_div (polyTranslate c P) (polyTranslate c Q) hQ0
  rw [← hshift, algebraMap_mul_single, HahnSeries.coeff_mul_single] at hcoeff
  rw [show (0 : ℤ) - (m : ℤ) = -(m : ℤ) from by ring, mul_one] at hcoeff
  show (algebraMap (RatFunc K) (LaurentSeries K) (ratFuncShift c g)).coeff (-(m : ℤ)) = _
  rw [hcoeff, polyTranslate_apply, polyTranslate_apply, Polynomial.eval_comp, Polynomial.eval_comp]
  simp

theorem regularAt_of_repr {g : RatFunc K} {c : K} {P Q : Polynomial K} (hQ : Q.eval c ≠ 0)
    (h : g = algebraMap (Polynomial K) (RatFunc K) P
      / algebraMap (Polynomial K) (RatFunc K) Q) : RegularAt g c := ⟨P, Q, hQ, h⟩

end

end GaloisForLFunctions.HTGeometry
