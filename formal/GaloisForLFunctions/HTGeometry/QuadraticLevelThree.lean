import GaloisForLFunctions.HTGeometry.JetLevelThreeDescent
import GaloisForLFunctions.HTGeometry.QuadraticTailShiftEquivalence
import GaloisForLFunctions.HTGeometry.QuadOneAffineTransport
import GaloisForLFunctions.HTGeometry.QuadTwoAffineTransport

/-!
# No normalizing shift at jet level three for the two quadratic maps

For `z ↦ z² + 1` and `z ↦ (z − 1)²` the third derivative vanishes and the second is the constant
`2`, so the inhomogeneous term produced by the level-three descent is

`R''' − (3/2)·(R'')²/R' = −3/(2·(z − crit))·2 = −3/(z − crit)`,

a simple pole at the critical point.  The resulting affine transport has exponent three, coefficient
the derivative — which vanishes to order one at the critical point — and an inhomogeneous term of
order `−1` there, so the critical-order obstruction applies and no such transport exists.

Together with the non-existence at level two this closes jet level three: every fixed element of the
substitution of jet order at most three is constant.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## `z ↦ z² + 1` -/

theorem quadOne_not_hasNormalizingShift_three :
    ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ 3 by omega) := by
  intro h
  rcases hasNormalizingShift_two_or_affineTransport_three _ quadOne_substitutionDeriv_ne_zero
      quadOne_pd_substitutionDeriv_ne_zero
      (fun g hg hgfix => quadOne_fixed_of_order_two hg hgfix) h with h2 | ⟨a, ha⟩
  · exact quadOne_not_hasNormalizingShift_two h2
  set R₀ : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne with hR₀def
  have hd1 : ratFuncDeriv R₀ = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne) :=
    ratFuncDeriv_algebraMap quadOne
  have hd2 : ratFuncDeriv (ratFuncDeriv R₀)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) := by
    rw [hd1, ratFuncDeriv_algebraMap, derivative_quadOne, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, mul_one, zero_add]
  have hd3 : ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R₀)) = 0 := by
    rw [hd2, ratFuncDeriv_algebraMap, Polynomial.derivative_C, map_zero]
  rw [hd3, hd2, hd1, zero_sub, sub_neg_eq_add] at ha
  set b : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne) with hbdef
  set c : RatFunc ℂ := RatFunc.C (3 / 2 : ℂ)
      * algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ^ 2 / b with hcdef
  have hb : b ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero quadOne_natDegree_ne_zero)
  have hAm2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 := by
    refine algebraMap_ne_zero_of_ne_zero ?_
    intro hh
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hh
    simp at this
  have hC32 : (RatFunc.C (3 / 2 : ℂ) : RatFunc ℂ) ≠ 0 := by
    intro hh
    have h32 : (3 / 2 : ℂ) = 0 := (RatFunc.C_injective (K := ℂ)) (by simp [hh])
    norm_num at h32
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (mul_ne_zero hC32 (pow_ne_zero 2 hAm2)) hb
  have hmultC : ∀ z : ℂ, Polynomial.rootMultiplicity z (Polynomial.C (2 : ℂ)) = 0 := by
    intro z
    refine Polynomial.rootMultiplicity_eq_zero ?_
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    norm_num
  have hcord : ∀ p : ℂ, ratOrder c p = -(Polynomial.rootMultiplicity p (Polynomial.derivative quadOne) : ℤ) := by
    intro p
    rw [hcdef, div_eq_mul_inv,
      ratOrder_mul (mul_ne_zero hC32 (pow_ne_zero 2 hAm2)) (inv_ne_zero hb),
      ratOrder_mul hC32 (pow_ne_zero 2 hAm2), ratOrder_C, ratOrder_pow hAm2,
      ratOrder_inv hb, ratOrder_algebraMap, ratOrder_algebraMap, hmultC p]
    norm_num
  have hbunit : ∀ p : ℂ, p ≠ 0 → ratOrder b p = 0 := by
    intro p hp
    rw [hbdef, ratOrder_algebraMap, Polynomial.rootMultiplicity_eq_zero ?_, Nat.cast_zero]
    rw [Polynomial.IsRoot.def, derivative_quadOne_eval]
    exact mul_ne_zero (by norm_num) hp
  have hbcrit : ratOrder b 0 = 1 := by
    rw [hbdef, ratOrder_algebraMap, rootMultiplicity_derivative_quadOne, Nat.cast_one]
  have hcreg : ∀ p : ℂ, p ≠ 0 → 0 ≤ ratOrder c p := by
    intro p hp
    rw [hcord p, Polynomial.rootMultiplicity_eq_zero ?_]
    · norm_num
    rw [Polynomial.IsRoot.def, derivative_quadOne_eval]
    exact mul_ne_zero (by norm_num) hp
  have hccrit : ratOrder c 0 = -1 := by
    rw [hcord, rootMultiplicity_derivative_quadOne, Nat.cast_one]
  have ha0 : a ≠ 0 := by
    intro hh
    rw [hh, map_zero, zero_mul, mul_zero, zero_add] at ha
    exact hc0 ha.symm
  have hIAT : IsAffineTransport quadOne quadOne_not_isConst 3 b c a := by
    show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
        quadOne_not_isConst a
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne)) ^ (3 : ℤ)
      = b * a + c
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ha
  exact quadOne_no_affineTransport_of_critical_order ha0 hb hc0 hIAT hbunit hcreg
    (by rw [hccrit, hbcrit]; norm_num) (by rw [hccrit]; norm_num)

/-! ## `z ↦ (z − 1)²` -/

theorem quadTwo_not_hasNormalizingShift_three :
    ¬ HasNormalizingShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_substitutionDeriv_ne_zero (show (1 : ℕ) ≤ 3 by omega) := by
  intro h
  rcases hasNormalizingShift_two_or_affineTransport_three _ quadTwo_substitutionDeriv_ne_zero
      quadTwo_pd_substitutionDeriv_ne_zero
      (fun g hg hgfix => quadTwo_fixed_of_order_two hg hgfix) h with h2 | ⟨a, ha⟩
  · exact quadTwo_not_hasNormalizingShift_two h2
  set R₀ : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo with hR₀def
  have hd1 : ratFuncDeriv R₀ = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo) :=
    ratFuncDeriv_algebraMap quadTwo
  have hd2 : ratFuncDeriv (ratFuncDeriv R₀)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) := by
    rw [hd1, ratFuncDeriv_algebraMap, derivative_quadTwo, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, zero_mul, mul_one, zero_add]
  have hd3 : ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R₀)) = 0 := by
    rw [hd2, ratFuncDeriv_algebraMap, Polynomial.derivative_C, map_zero]
  rw [hd3, hd2, hd1, zero_sub, sub_neg_eq_add] at ha
  set b : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo) with hbdef
  set c : RatFunc ℂ := RatFunc.C (3 / 2 : ℂ)
      * algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ^ 2 / b with hcdef
  have hb : b ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero quadTwo_natDegree_ne_zero)
  have hAm2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 2) ≠ 0 := by
    refine algebraMap_ne_zero_of_ne_zero ?_
    intro hh
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hh
    simp at this
  have hC32 : (RatFunc.C (3 / 2 : ℂ) : RatFunc ℂ) ≠ 0 := by
    intro hh
    have h32 : (3 / 2 : ℂ) = 0 := (RatFunc.C_injective (K := ℂ)) (by simp [hh])
    norm_num at h32
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (mul_ne_zero hC32 (pow_ne_zero 2 hAm2)) hb
  have hmultC : ∀ z : ℂ, Polynomial.rootMultiplicity z (Polynomial.C (2 : ℂ)) = 0 := by
    intro z
    refine Polynomial.rootMultiplicity_eq_zero ?_
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    norm_num
  have hcord : ∀ p : ℂ, ratOrder c p = -(Polynomial.rootMultiplicity p (Polynomial.derivative quadTwo) : ℤ) := by
    intro p
    rw [hcdef, div_eq_mul_inv,
      ratOrder_mul (mul_ne_zero hC32 (pow_ne_zero 2 hAm2)) (inv_ne_zero hb),
      ratOrder_mul hC32 (pow_ne_zero 2 hAm2), ratOrder_C, ratOrder_pow hAm2,
      ratOrder_inv hb, ratOrder_algebraMap, ratOrder_algebraMap, hmultC p]
    norm_num
  have hbunit : ∀ p : ℂ, p ≠ 1 → ratOrder b p = 0 := by
    intro p hp
    rw [hbdef, ratOrder_algebraMap, Polynomial.rootMultiplicity_eq_zero ?_, Nat.cast_zero]
    rw [Polynomial.IsRoot.def, derivative_quadTwo_eval]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hp)
  have hbcrit : ratOrder b 1 = 1 := by
    rw [hbdef, ratOrder_algebraMap, rootMultiplicity_derivative_quadTwo, Nat.cast_one]
  have hcreg : ∀ p : ℂ, p ≠ 1 → 0 ≤ ratOrder c p := by
    intro p hp
    rw [hcord p, Polynomial.rootMultiplicity_eq_zero ?_]
    · norm_num
    rw [Polynomial.IsRoot.def, derivative_quadTwo_eval]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hp)
  have hccrit : ratOrder c 1 = -1 := by
    rw [hcord, rootMultiplicity_derivative_quadTwo, Nat.cast_one]
  have ha0 : a ≠ 0 := by
    intro hh
    rw [hh, map_zero, zero_mul, mul_zero, zero_add] at ha
    exact hc0 ha.symm
  have hIAT : IsAffineTransport quadTwo quadTwo_not_isConst 3 b c a := by
    show ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
        quadTwo_not_isConst a
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo)) ^ (3 : ℤ)
      = b * a + c
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ha
  exact quadTwo_no_affineTransport_of_critical_order ha0 hb hc0 hIAT hbunit hcreg
    (by rw [hccrit, hbcrit]; norm_num) (by rw [hccrit]; norm_num)

end

end GaloisForLFunctions.HTGeometry
